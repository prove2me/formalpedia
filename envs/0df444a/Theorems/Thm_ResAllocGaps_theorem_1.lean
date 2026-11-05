-- Prove2me | Theorems.Thm_ResAllocGaps_theorem_1
-- name    : ResAllocGaps.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:18.159163+00:00
-- url     : https://prove2.me/theorems/071b0c5f-77e5-43e6-9ca4-7a9d99cbc496
-- title:
--   Theorem 1 (universal lower bound) — regret $\Omega(T^{1/2-1/(2(1+\beta))})$ for $\beta>0$ and $\Omega(\log T)$ for $\beta=0$
-- statement:
--   There is a universal constant $c>0$ such that for every $\beta\ge0$ there are a candidate-ability distribution $F\in\mathscr F_{\beta,1/2}$ on $[0,1]$ and a horizon $T_0<\infty$ such that for every $T\ge T_0$ some budget $B\in[T]$ makes every feasible online policy $\pi\in\Pi(B,T)$ pay
--   $$\mathrm{Regret}(B,T;\pi)\ \ge\ \frac{c}{1+\beta}\,T^{\frac12-\frac1{2(\beta+1)}}\ \mathbb 1\{\beta>0\}\ +\ c\log T\ \mathbb 1\{\beta=0\}.$$
--   Here $\delta=0$, $\varepsilon_0=\tfrac12$, the multisecretary problem selects at most $B$ of $T$ i.i.d. candidates online (randomization allowed), and regret is measured against the hindsight optimum.
--
--   As $\beta$ runs over $[0,\infty)$ the exponent runs over $[0,\tfrac12)$: the shape of the ability distribution near its gaps alone forces polynomial regret, whatever the policy.
--
--   **Formalization Note** The distribution is a probability measure $\mu$ on $\mathbb R$ with $\mu([0,1])=1$ and `IsClustered μ β (1/2) 0`. Online policies are `OnlinePolicy μ T B`.
--
--   Differences from the source:
--   - reading: a universal constant c > 0, introduced after 'consider any β' → ∃ c > 0 before ∀ β ≥ 0; reason: 'universal' and the explicit factor 1/(1 + β) say c does not depend on β; the proof's probabilities are β-free and α₀ ≥ ln(129/128)/(1 + β); this is the stronger reading
--   - reading: for any online policy π ∈ Π(B, T), sup_{B∈[T]} Regret(B, T; π) → ∃ B ∈ [1, T], ∀ π ∈ Π(B, T), Regret(B, T; π) ≥ bound; reason: π depends on the B bound by the sup; over the finite set [T], 'for every family (π_B)_B, max_B Regret(B, T; π_B) ≥ bound' is equivalent by choice to this form
--   - encoding: (c/(1+β))T^{1/2−1/(2(β+1))}1{β > 0} + c log T 1{β = 0} → if 0 < β then c/(1+β) · T^(1/2 − 1/(2(β+1))) else c · Real.log T; reason: β ≥ 0, so the two indicators are the two branches; natural log (the base only rescales c); Real.rpow
--   - encoding: F ∈ 𝓕_{β,ε₀} with ε₀ = 1/2, δ = 0, a candidate-ability distribution on [0, 1] → ∃ μ, IsProbabilityMeasure μ ∧ μ([0, 1]) = 1 ∧ IsClustered μ β (1/2) 0; reason: the paper's standing assumption that abilities lie in [0, 1] (abstract; p.10–11); same distributions
--   - encoding: times t = 1, …, T; requests θ_t and seeds U_t; actions in {reject, accept}; Π(B, T) of p.8 → index t − 1 : Fin T; sample Fin T → ℝ × ℝ with law (μ ⊗ Unif[0,1])^{⊗T}; accept bits (Bool) measurable in the observed prefix; at most B acceptances almost surely (OnlinePolicy); reason: Lean convention; by Doob–Dynkin these are exactly the 𝓕_t-measurable actions of p.8, so the same policies
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, §3.2, Theorem 1, p.14 (proof Appendix EC.1, pp.ec1–ec10)

import Mathlib
import Definitions.Def_ResAllocGaps_quantile
import Definitions.Def_ResAllocGaps_IsClustered
import Definitions.Def_ResAllocGaps_OnlinePolicy

open MeasureTheory

namespace ResAllocGaps

/-- **Theorem 1 (universal lower bound)**, Besbes, Kanoria & Kumar, arXiv:2205.09078v2, §3.2, p.14:
"Fix `δ = 0`, `ε₀ = 1/2` and consider any `β ∈ [0, ∞)`. Then there exists a candidate-ability
distribution `F ∈ 𝓕_{β,ε₀}`, a time horizon `T₀ < ∞`, a universal constant `c > 0` such that, for
all `T ≥ T₀` and for any online policy `π ∈ Π(B, T)`, we have that
`sup_{B∈[T]} Regret(B, T; π) ≥ (c/(1 + β)) T^{1/2 − 1/(2(β+1))} 1{β > 0} + c log T 1{β = 0}`."

**Formalization Note.** The universal constant `c` is chosen before `β`. The candidate-ability
distribution is a probability measure `μ` on `ℝ` with `μ([0, 1]) = 1` (abilities lie in `[0, 1]`)
and `IsClustered μ β (1/2) 0`, i.e. `F ∈ 𝓕_{β,1/2}`. The supremum over `B ∈ [T]` with a policy for
each budget is stated as "there is `B ∈ [1, T]` such that every `π ∈ Π(B, T)` has regret at least
the bound"; over the finite set `[T]` this is equivalent (by choice) to: for every family
`(π_B ∈ Π(B, T))_{B ∈ [T]}`, `max_B Regret(B, T; π_B)` is at least the bound. The indicators are an
`if` on `0 < β` (with `β ≥ 0`), `log` is `Real.log` and `T^x` is `Real.rpow`. Online policies are
randomized (they read the seeds `U_t`) and measurable in the observed prefix (`OnlinePolicy`). -/
theorem theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 0 ≤ β →
      ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Icc 0 1) = 1 ∧
        IsClustered μ β (1 / 2) 0 ∧
        ∃ T₀ : ℕ, ∀ T ≥ T₀, ∃ B ∈ Finset.Icc 1 T, ∀ π : OnlinePolicy μ T B,
          (if 0 < β then c / (1 + β) * (T : ℝ) ^ ((1 : ℝ) / 2 - 1 / (2 * (β + 1)))
            else c * Real.log T) ≤ regret π := by sorry

end ResAllocGaps
