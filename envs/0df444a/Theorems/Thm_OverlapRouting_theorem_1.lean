-- Prove2me | Theorems.Thm_OverlapRouting_theorem_1
-- name    : OverlapRouting.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:18.939221+00:00
-- url     : https://prove2.me/theorems/9a0ae74e-0637-42ca-a5aa-7fc5b9ba5d26
-- title:
--   Theorem 1 — $Z^{AO(\alpha)}/Z^*\to Qr^\infty_{avg}/(N'\mu)$ almost surely
-- statement:
--   Fix $N'\ge1$ customers per vehicle, a capacity $Q\ge1$, a demand law $D$ on $\{0,\dots,u\}$ with mean $\mu>0$ and a depot $x_0$. Let the customer locations $X_0,X_1,\dots$ be i.i.d. random points of the plane that lie almost surely in a compact set $\mathcal A$, with $\mathbb P(X_0\ne x_0)>0$; the instance with $M$ vehicles has the $N=N'M$ customers $X_0,\dots,X_{N-1}$. Then:
--
--   1. the limit $r^\infty_{avg}=\lim_{M\to\infty}r_{avg}$ of the average expected number of trips per vehicle exists, and
--   2. almost surely, for every $\alpha$ and every sequence of labellings that is α-optimal for every $M\ge1$,
--   $$\lim_{M\to\infty}\frac{Z^{AO(\alpha)}}{Z^*}=\frac{Q\,r^\infty_{avg}}{N'\mu}.$$
--
--   Here $Z^{AO(\alpha)}$ is the expected cost of adjacent overlapping routes served by Algorithm 1, and $Z^*$ that of full reoptimization (the split-delivery VRP optimum for each day's demand). The asymptotic cost ratio is thus determined by the average number of trips per vehicle alone.
--
--   **Formalization Note** The labellings may be chosen after the locations and need not be measurable.
--
--   Differences from the source:
--   - reading: "D can only take non-negative integer values and has finite support {0} ∪ [u]" (p.5) → any probability mass function p on {0,…,u} (values may have mass 0); reason: the authors' own usage in Appendix A, p.34 (WLOG aperiodic, P[D̄ > Q] > 0); the more general reading, which contains the literal one
--   - reading: "lim" with random customer locations → almost sure convergence; reason: the strongest mode; the proof's probabilistic inputs (BHH, SLLN) are almost sure
--   - reading: x₁,…,x_N i.i.d. for each M → the first N′M points of one i.i.d. sequence; reason: the standard coupling under which an almost sure limit in M is meaningful; the paper's BHH citation uses it
--   - generalization: one α-optimal labelling for each M (p.13) → every real α and every sequence of α-optimal labellings, inside the almost sure event; reason: the limit holds uniformly over these choices; specializes to any fixed choice
--   - encoding: r∞_avg = lim r_avg (p.16), its existence taken for granted → ∃ r∞ with r_avg → r∞, as part of the conclusion; reason: makes the existence of the limit part of the theorem
--   - encoding: "compact support 𝒜" → Xᵢ ∈ 𝒜 almost surely for a compact 𝒜; reason: the support is then contained in 𝒜; same instances
--   - encoding: µ in a denominator; the ratio Z^{AO(α)}/Z* → hypotheses µ > 0 and ℙ(X₀ ≠ x₀) > 0; reason: they only exclude the case Z^{AO(α)} = Z* = 0, where the ratio is 0/0
--   - encoding: customers labelled 1,…,N along the tour, vehicles j = 1,…,M → 0-based labels 0,…,N′M−1 given by a permutation ℓ (label k is customer ℓ k); 1-based vehicle indices; reason: Lean convention; same instances
--   - encoding: "Z* … travel cost of reoptimization" (pp.11–12) → expectation over the demand vector of the infimum of the total length of split-delivery solutions with real delivered amounts; reason: the literal "splittable" model of p.6; for integer demands the bounds of Lemmas 1–2 bracket the integer-amount optimum as well
--   - encoding: Z^{AO(α)}, the expected travel cost of AO under Algorithm 1 → expectation over the demand vector of the length of the routes Algorithm 1 drives (refill exactly at a stock-out, zero-demand customers skipped); reason: the route of p.10 (rules 1–3) and Algorithm 1, line 13
--   - encoding: E[Rⱼ], the expected number of trips of vehicle j → expTrips: the expectation of rⱼ = ⌈wⱼ/Q⌉ from the recursion (3), over i.i.d. demands; reason: (3) is the paper's own definition of the trip count; Eq. (3) milestone ties it to the driven routes
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Theorem 1, p.17 (proof pp.17–18); r∞_avg defined on p.16

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OverlapRouting

/-- **Theorem 1**, p.17 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)): "Consider a
sequence of integer `M` going to infinity, and fix `N/M = N′` to be some positive integer. Let the
customer locations `x₁, x₂, …, x_N` be a sequence of i.i.d. random vectors with compact support
`𝒜`. Then we have `lim_{M→∞} Z^{AO(α)}/Z* = Q r∞_avg / (N′µ)`."

Let `N′ ≥ 1`, `Q ≥ 1`, the demand law `D` have mean `µ > 0`, and let the customer locations
`X₀, X₁, …` be i.i.d. random points of the plane, almost surely in a compact set `𝒜`, with
`ℙ(X₀ ≠ x₀) > 0`. Then
1. the limit `r∞_avg = lim_{M→∞} r_avg` exists, and
2. almost surely, for every `α` and every sequence of labellings `ℓ_M` that are `α`-optimal for
   the first `N′M` locations, `Z^{AO(α)}/Z* → Q r∞_avg/(N′µ)` as `M → ∞`.

**Formalization Note.** The `M`-th instance uses the first `N′M` points of one i.i.d. sequence.
"lim" is read as almost sure convergence; the labellings are chosen after the locations and need
not be measurable. "Compact support `𝒜`" is encoded as `Xᵢ ∈ 𝒜` almost surely for a compact `𝒜`.
`µ > 0` and `ℙ(X₀ ≠ x₀) > 0` exclude only the case `Z^{AO(α)} = Z* = 0`. -/
theorem theorem_1 (N' Q : ℕ) (hN' : 1 ≤ N') (hQ : 1 ≤ Q) (D : DemandLaw) (hμ : 0 < D.mean)
    (x₀ : Point) (A : Set Point) (hA : IsCompact A)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → Point) (hXmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X Pr)
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr) (hsupp : ∀ i, ∀ᵐ ω ∂Pr, X i ω ∈ A)
    (hnondeg : 0 < Pr {ω | X 0 ω ≠ x₀}) :
    ∃ rInf : ℝ, Tendsto (fun M : ℕ => rAvg N' Q D M) atTop (𝓝 rInf) ∧
      ∀ᵐ ω ∂Pr, ∀ (α : ℝ) (ℓ : (M : ℕ) → Equiv.Perm (Fin (N' * M))),
        (∀ M, 1 ≤ M → IsAlphaOptimal α (fun i : Fin (N' * M) => X i ω) (ℓ M)) →
        Tendsto (fun M : ℕ => ZAO N' Q D x₀ M (fun i : Fin (N' * M) => X i ω) (ℓ M) /
            Zstar Q D x₀ (fun i : Fin (N' * M) => X i ω)) atTop
          (𝓝 ((Q : ℝ) * rInf / ((N' : ℝ) * D.mean))) := by sorry

end OverlapRouting
