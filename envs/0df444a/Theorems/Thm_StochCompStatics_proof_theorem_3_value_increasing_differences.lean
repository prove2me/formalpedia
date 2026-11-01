-- Prove2me | Theorems.Thm_StochCompStatics_proof_theorem_3_value_increasing_differences
-- name    : StochCompStatics.proof_theorem_3_value_increasing_differences
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:37.24848+00:00
-- url     : https://prove2.me/theorems/9112218d-47a8-4492-bc65-03e7c992247d
-- title:
--   Proof of Theorem 3, pp.21–22 — $V(s,\beta)$ has increasing differences in $(s,\beta)$ and is increasing in $s$
-- statement:
--   Let $(S,A,\Gamma,p,r)$ satisfy Assumption 1 with $\Gamma$ ascending, and for every discount factor $\beta\in(0,1)$ let $V(\cdot,\beta)$ satisfy the standing assumptions (the iterates $T_\beta^n0$ converge uniformly to $V(\cdot,\beta)$, with all maxima attained and all iterates measurable and integrable). Then the value function $V(s,\beta)$ has increasing differences in $(s,\beta)$ on $S\times(0,1)$:
--   $$
--   V(s_2,\beta_2)-V(s_2,\beta_1)\ge V(s_1,\beta_2)-V(s_1,\beta_1)\qquad(s_1\le s_2,\ \beta_1\le\beta_2),
--   $$
--   and $V(\cdot,\beta)$ is increasing in $s$ for every $\beta$.
--
--   From this the paper concludes that $h(s,a,\beta,V)$ has increasing differences in $(a,\beta)$, which makes the policy function increasing in the discount factor.
--
--   Differences from the source:
--   - generalization: state space S ⊆ ℝⁿ a Borel set with the componentwise order → any measurable space S with a partial order; reason: the paper's S with the Borel σ-algebra and the componentwise order is an instance
--   - encoding: action space A ⊆ ℝ, p and r defined on S × A → A : Set ℝ, p a Markov kernel on S × ℝ, r : S → ℝ → ℝ, every hypothesis on p and r imposed for a ∈ A only; reason: values of p and r at actions outside A are never used; same instances
--   - generalization: Γ a measurable subset of S × A with measurable sections; r measurable → not assumed; reason: no step uses these measurability conditions; every instance of the paper is covered
--   - encoding: Tf(s) = max_{a∈Γ(s)} h(s, a, f) → bellman = sSup of the image h(s, Γ(s), f), with the attainment of the maximum as a hypothesis wherever the paper writes max; reason: the paper's max presupposes attainment; sSup equals the maximum when it is attained
--   - generalization: V is the unique continuous solution of TV = V, Tⁿf → V uniformly for every f ∈ B(S), and V(s) = sup_σ V_σ(s) → StandingAssumptions: Tⁿ0 → V uniformly, V = TV with the maximum attained, the maxima along Tⁿ0 attained; continuity and uniqueness not assumed; reason: only f = 0 and the Bellman equation are used; a uniform limit is unique, so V is the paper's value function under its standing assumptions
--   - reading: footnote 9: all functions are assumed to be integrable → Tⁿ0 and V measurable and integrable against every p(s, a), a ∈ A; reason: the integrals in h and T are the Bochner integral, which is 0 for a non-integrable function; these are the integrals the paper writes
--   - reading: p monotone: for every increasing f, ∫ f(s′)p(s, a, ds′) is increasing in (s, a) → for every increasing measurable f integrable against every p(s, a), a ∈ A, the integral is monotone on S × A; reason: footnote 9: the integral of f exists only for such f
-- source:
--   Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, Proof of Theorem 3, pp.21–22 (Appendix §6.2)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
import Definitions.Def_StochCompStatics_Model

namespace StochCompStatics

open MeasureTheory ProbabilityTheory Supermodularity.Monotonicity

/-- Proof of Theorem 3(i) (Light, Stochastic Comparative Statics in Markov Decision Processes,
arXiv:1904.05481v2, Appendix §6.2, pp.21–22): under Assumption 1 with `Γ` ascending, for all
`n`, `Tⁿf` has increasing differences in `(s, β)` and is increasing in `s`; since `Tⁿf → V`
uniformly, the value function `V(s, β)` has increasing differences in `(s, β)` and is increasing
in `s`.

**Formalization Note** `V β` is the value function `s ↦ V(s, β)` for the discount factor
`β ∈ (0, 1)`, and it satisfies the standing assumptions of p.6 and footnote 9 for every such `β`
(`StandingAssumptions`, with the iterates `Tⁿ0`). -/
theorem proof_theorem_3_value_increasing_differences {S : Type*} [MeasurableSpace S]
    [PartialOrder S] (A : Set ℝ) (Γ : S → Set ℝ) (p : Kernel (S × ℝ) S) [IsMarkovKernel p]
    (r : S → ℝ → ℝ) (V : ℝ → S → ℝ) (hΓ : IsActionCorr A Γ) (hA1 : Assumption1 A Γ p r)
    (hasc : IsAscending Γ)
    (hSt : ∀ β ∈ Set.Ioo (0 : ℝ) 1, StandingAssumptions A Γ p r β (V β)) :
    IncreasingDifferencesOn (fun s β => V β s) (Set.univ ×ˢ Set.Ioo 0 1) ∧
    ∀ β ∈ Set.Ioo (0 : ℝ) 1, Monotone (V β) := by sorry

end StochCompStatics
