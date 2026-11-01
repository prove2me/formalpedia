-- Prove2me | Theorems.Thm_StochCompStatics_proposition_5
-- name    : StochCompStatics.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:13.264416+00:00
-- url     : https://prove2.me/theorems/60a82c6f-0b1d-45a5-83fb-6e5737ea0aa2
-- title:
--   Proposition 5 — $h$ has increasing differences, $G$ is ascending, $Tf$ and $V$ are increasing (corrected: $\Gamma$ ascending in (ii))
-- statement:
--   Let $(S,A,\Gamma,p,r,\beta)$ be a discounted dynamic program with $0<\beta<1$ that satisfies Assumption 1, let $V$ satisfy the standing assumptions, and let $g(s)=\max G(s)$. Then:
--
--   1. $h(s,a,f)$ has increasing differences in $(s,a)$ on $S\times A$ whenever $f$ is an increasing (measurable, $p$-integrable) function;
--   2. if $\Gamma$ is ascending, then $G$ is ascending, and in particular $g(s)=\max G(s)$ is an increasing function;
--   3. $Tf(s)=\max_{a\in\Gamma(s)}h(s,a,f)$ is an increasing function whenever $f$ is an increasing (measurable, $p$-integrable) function whose maximum is attained, and $V$ is an increasing function.
--
--   These are the monotonicity properties of the Bellman operator that the proof of Theorem 3 combines with Proposition 6; the paper refers to Topkis (2011), Theorem 3.9.2.
--
--   Differences from the source:
--   - correction: (ii) G(s) is ascending, under Assumption 1 alone → (ii) under Assumption 1 and Γ ascending; reason: false as printed: S = {0 < 1}, Γ(0) = {1}, Γ(1) = {0, 1}, p ≡ δ₀, r(0,0) = 200, r(0,1) = 0, r(1,0) = 201, r(1,1) = 100 satisfy Assumption 1 and give G(0) = {1}, G(1) = {0}, so g is decreasing; Theorem 3 assumes Γ ascending
--   - generalization: state space S ⊆ ℝⁿ a Borel set with the componentwise order → any measurable space S with a partial order; reason: the paper's S with the Borel σ-algebra and the componentwise order is an instance
--   - encoding: action space A ⊆ ℝ, p and r defined on S × A → A : Set ℝ, p a Markov kernel on S × ℝ, r : S → ℝ → ℝ, every hypothesis on p and r imposed for a ∈ A only; reason: values of p and r at actions outside A are never used; same instances
--   - generalization: Γ a measurable subset of S × A with measurable sections; r measurable → not assumed; reason: no step uses these measurability conditions; every instance of the paper is covered
--   - encoding: Tf(s) = max_{a∈Γ(s)} h(s, a, f) → bellman = sSup of the image h(s, Γ(s), f), with the attainment of the maximum as a hypothesis wherever the paper writes max; reason: the paper's max presupposes attainment; sSup equals the maximum when it is attained
--   - generalization: V is the unique continuous solution of TV = V, Tⁿf → V uniformly for every f ∈ B(S), and V(s) = sup_σ V_σ(s) → StandingAssumptions: Tⁿ0 → V uniformly, V = TV with the maximum attained, the maxima along Tⁿ0 attained; continuity and uniqueness not assumed; reason: only f = 0 and the Bellman equation are used; a uniform limit is unique, so V is the paper's value function under its standing assumptions
--   - reading: footnote 9: all functions are assumed to be integrable → Tⁿ0 and V measurable and integrable against every p(s, a), a ∈ A; in (i) and (iii) the increasing f measurable and integrable against every p(s, a), a ∈ A; reason: the integrals in h and T are the Bochner integral, which is 0 for a non-integrable function; these are the integrals the paper writes
--   - reading: p monotone: for every increasing f, ∫ f(s′)p(s, a, ds′) is increasing in (s, a) → for every increasing measurable f integrable against every p(s, a), a ∈ A, the integral is monotone on S × A; reason: footnote 9: the integral of f exists only for such f
-- source:
--   Light, Stochastic Comparative Statics in Markov Decision Processes, arXiv:1904.05481v2, Proposition 5, p.20 (Appendix §6.2)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn
import Definitions.Def_StochCompStatics_Model

namespace StochCompStatics

open MeasureTheory ProbabilityTheory Supermodularity.Monotonicity

/-- Proposition 5 (Light, Stochastic Comparative Statics in Markov Decision Processes,
arXiv:1904.05481v2, Appendix §6.2, p.20), corrected: suppose that Assumption 1 holds. Then
(i) `h(s, a, f)` has increasing differences in `(s, a)` whenever `f` is increasing;
(ii) if `Γ` is ascending, then `G` is ascending, and `g(s) = max G(s)` is increasing;
(iii) `Tf(s) = max_{a ∈ Γ(s)} h(s, a, f)` is increasing whenever `f` is increasing, and `V` is
increasing.

**Formalization Note** Part (ii) is false as printed without "`Γ` ascending": two states
`0 < 1`, `Γ(0) = {1}`, `Γ(1) = {0, 1}`, `p ≡ δ₀`, `r(0,0) = 200`, `r(0,1) = 0`, `r(1,0) = 201`,
`r(1,1) = 100` satisfy Assumption 1 and give `G(0) = {1}`, `G(1) = {0}`. The hypothesis is added to
(ii) only; Theorem 3 assumes it. The functions `f` in (i) and (iii) are measurable and integrable
against every `p(s, a)`, `a ∈ A` (footnote 9), and in (iii) the maximum defining `Tf` is attained.
`V` and `g` satisfy the standing assumptions of p.6. -/
theorem proposition_5 {S : Type*} [MeasurableSpace S] [PartialOrder S] (A : Set ℝ)
    (Γ : S → Set ℝ) (p : Kernel (S × ℝ) S) [IsMarkovKernel p] (r : S → ℝ → ℝ) (β : ℝ)
    (V g : S → ℝ) (hβ₀ : 0 < β) (hβ₁ : β < 1) (hΓ : IsActionCorr A Γ)
    (hA1 : Assumption1 A Γ p r) (hSt : StandingAssumptions A Γ p r β V)
    (hg : ∀ s, IsGreatest (optSet Γ p r β V s) (g s)) :
    (∀ f : S → ℝ, Monotone f → Measurable f → (∀ s, ∀ a ∈ A, Integrable f (p (s, a))) →
      IncreasingDifferencesOn (h p r β f) (Set.univ ×ˢ A)) ∧
    (IsAscending Γ → IsAscending (optSet Γ p r β V) ∧ Monotone g) ∧
    (∀ f : S → ℝ, Monotone f → Measurable f → (∀ s, ∀ a ∈ A, Integrable f (p (s, a))) →
      (∀ s, ∃ a ∈ Γ s, IsGreatest (h p r β f s '' Γ s) (h p r β f s a)) →
      Monotone (bellman Γ p r β f)) ∧
    Monotone V := by sorry

end StochCompStatics
