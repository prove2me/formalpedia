-- Prove2me | Theorems.Thm_OverlapRouting_theorem_1_error_vanishes
-- name    : OverlapRouting.theorem_1_error_vanishes
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:34:59.417821+00:00
-- url     : https://prove2.me/theorems/82ed7485-7206-4ee9-8027-0fe05a9ce98a
-- title:
--   Proof of Theorem 1 — the error term $(*)$ goes to $0$ almost surely
-- statement:
--   Let $N'\ge1$, $Q\ge1$, $D$ a demand law with mean $\mu>0$, $x_0$ the depot, and let $X_0,X_1,\dots$ be i.i.d. random points of the plane that lie almost surely in a compact set $\mathcal A$, with $\mathbb P(X_0\ne x_0)>0$. For $M\ge1$ put $N=N'M$, let $L^*_M$ be the optimal TSP tour length through $X_0,\dots,X_{N-1}$ and $c_i=\|x_0-X_i\|_2$. Then almost surely, for all real constants $a$ and $b$,
--   $$\frac{a+b\,L^*_M}{\frac{2\mu}{Q}\sum_{i=0}^{N-1}c_i}\ \longrightarrow\ 0\qquad(M\to\infty).$$
--
--   Every term of the bounds of Proposition 1, Lemma 5 and Lemma 2 other than the leading one has the form $a+bL^*$ with $a,b$ independent of $M$ (using $r_{avg}\le\mathbb E[R_1]$), so this is the step "$(*)$ goes to $0$" of the proof of Theorem 1, for both inequalities.
--
--   Differences from the source:
--   - generalization: (∗) ≤ (2Γ₃c_max + α(2E[R₁] + 2Γ₃ + 3)L*) / ((2µ/Q)Σcᵢ) goes to 0 → (a + bL*)/((2µ/Q)Σcᵢ) → 0 for all real a, b simultaneously, almost surely; reason: the paper's numerators are of this form (c_max ≤ sup over 𝒜 is a constant); specializes to (∗) and to the p.18 terms
--   - reading: "(∗) goes to 0" with random locations → almost sure convergence; reason: the strongest mode; BHH and the SLLN that the paper uses are almost sure statements
--   - reading: x₁,…,x_N i.i.d. for each M → the first N′M points of one i.i.d. sequence; reason: the standard coupling under which an almost sure limit in M is meaningful; the paper's BHH citation uses it
--   - encoding: "compact support 𝒜" → Xᵢ ∈ 𝒜 almost surely for a compact 𝒜; reason: the support is then contained in 𝒜; same instances
--   - encoding: µ and Σcᵢ in denominators → hypotheses µ > 0 and ℙ(X₀ ≠ x₀) > 0; reason: they only exclude the degenerate case Σcᵢ = 0 for all M (or µ = 0), where (∗) is 0/0
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, proof of Theorem 1, p.17 (display of (∗) and "This implies that (∗) goes to 0 as M goes to infinity"), and its use on p.18

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OverlapRouting

/-- **Proof of Theorem 1**, p.17 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)): "This
implies that `(∗)` goes to 0 as `M` goes to infinity", for
`(∗) ≤ (2Γ₃c_max + α(2E[R₁] + 2Γ₃ + 3)L*) / ((2µ/Q) ∑_{i=1}^{N} cᵢ)`.

Let the customer locations `X₀, X₁, …` be i.i.d. random points of the plane, almost surely in a
compact set `𝒜`, with `ℙ(X₀ ≠ x₀) > 0`, and let `µ > 0`. Then almost surely, for all real constants
`a` and `b`, with `N = N′M`, `L*` the optimal tour through `X₀, …, X_{N−1}` and `cᵢ = ‖x₀ − Xᵢ‖`,
`(a + b L*) / ((2µ/Q) ∑_{i<N} cᵢ) → 0` as `M → ∞`.

This covers the numerators of both halves of the proof (pp.17–18): every term other than the
leading one has the form `a + bL*` with `a, b` independent of `M`.

**Formalization Note.** The `M`-th instance uses the first `N′M` points of one i.i.d. sequence.
"Compact support `𝒜`" is encoded as `Xᵢ ∈ 𝒜` almost surely for a compact `𝒜`. -/
theorem theorem_1_error_vanishes (N' Q : ℕ) (hN' : 1 ≤ N') (hQ : 1 ≤ Q) (D : DemandLaw)
    (hμ : 0 < D.mean) (x₀ : Point) (A : Set Point) (hA : IsCompact A)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → Point) (hXmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X Pr)
    (hident : ∀ i, IdentDistrib (X i) (X 0) Pr Pr) (hsupp : ∀ i, ∀ᵐ ω ∂Pr, X i ω ∈ A)
    (hnondeg : 0 < Pr {ω | X 0 ω ≠ x₀}) :
    ∀ᵐ ω ∂Pr, ∀ a b : ℝ, Tendsto (fun M : ℕ =>
      (a + b * tspOpt (fun i : Fin (N' * M) => X i ω)) /
        (2 * D.mean / Q * ∑ i : Fin (N' * M), dist x₀ (X i ω))) atTop (𝓝 0) := by sorry

end OverlapRouting
