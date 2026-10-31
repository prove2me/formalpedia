-- Prove2me | Theorems.Thm_SeqExpDiffusion_theorem_2
-- name    : SeqExpDiffusion.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:11.362016+00:00
-- url     : https://prove2.me/theorems/974fbe3a-eb74-43c3-b89a-6b8406f625e0
-- title:
--   Theorem 2 — $\tilde V=\max_{\{a_i,a_j\}}\tilde{\mathcal G}_{ij}$ is in $\widehat{\mathcal C}^2$ and equals the value $\tilde{\mathcal G}$ (corrected: thresholds of (18))
-- statement:
--   Let $\mathscr A$ be a finite set of at least two actions with affine, non-dominated expected rewards $\tilde R_a(\delta)=\tilde\alpha_a+\tilde\beta_a\delta$, let $r>0$, $\tilde\sigma>0$, and assume the payoff $G=\max_a\tilde R_a$ is nonnegative on $[0,1]$. Then there is a family $(\tilde{\mathcal G}_{ij})_{i\ne j}$ such that
--
--   1. each $\tilde{\mathcal G}_{ij}$ is the value function of (12) with the two-action payoff $\tilde G_{ij}=\max\{\tilde R_i,\tilde R_j\}$;
--   2. whenever $\tilde\beta_i<\tilde\beta_j$ and $\tilde G_{ij}\ge0$ on $[0,1]$, $\tilde{\mathcal G}_{ij}$ is the closed form (18) of Proposition 5 on $[0,1]$, with an admissible quadruple $(\underline\delta_{ij},\bar\delta_{ij},C^0_{ij},C^1_{ij})$;
--   3. the function $\tilde V(\delta)=\max_{\{a_i,a_j\}\subseteq\mathscr A}\tilde{\mathcal G}_{ij}(\delta)$ is in $\widehat{\mathcal C}^2$;
--   4. as a result,
--   $$\tilde{\mathcal G}(\delta)=\tilde V(\delta)\qquad\text{for all }\delta\in[0,1],$$
--   where $\tilde{\mathcal G}$ is the value function of the optimal stopping problem (12) with payoff $G$.
--
--   Solving the stopping problem with $|\mathscr A|$ actions therefore reduces to $|\mathscr A|(|\mathscr A|-1)$ two-action problems, each solved in closed form.
--
--   Differences from the source:
--   - correction: the 𝒢̃_ij of Proposition 5 have δ̲_ij, δ̄_ij ∈ (0, 1) and positive constants → the admissible quadruple of IsTwoActionForm, where a threshold is 0 or 1 exactly when the corresponding reward is identically 0; reason: counterexample to the printed Proposition 5: R̃_i ≡ 0, R̃_j(δ) = 2δ − 1 (see proposition_5)
--   - generalization: G̃_ij ≥ 0 on [0, 1] for every pair, "without loss of generality" (p.19) → only G ≥ 0 on [0, 1]; the closed form (18) is asserted for the nonnegative pairs, and every 𝒢̃_ij is the value of its two-action problem; reason: in the paper's setting every pair is nonnegative, so the statement specializes to it; the printed assumption is not without loss (Figure 4's data has G̃₁₂(1) = −1)
--   - reading: 𝒢̃_ij, "the function in Proposition 5", "is the value function of a problem in which only actions a_i and a_j are available" (p.21, (A-7)) → clause 1: 𝒢̃_ij is the value function of (12) with payoff G̃_ij; reason: the page defines Ṽ from these values
--   - encoding: |𝒜| ≥ 2 and the maximum over unordered pairs {a_i, a_j} → a nontrivial finite type and the maximum over ordered pairs i ≠ j; reason: both orders of a pair carry the same problem
--   - generalization: stopping times of the filtration 𝔽 of the experimentation history (p.8) → every probability space and every filtration for which the driving motion is Brownian; reason: the paper's setting is one instance, so the statement specializes to it
--   - reading: (12) is silent on the event τ = ∞ → the reward is 0 on {τ = ∞}; reason: the payoffs are bounded, so this changes no supremum relative to finite stopping times
--   - encoding: the value 𝒢̃ = sup over stopping times of a solution of (12) → least upper bound over [0, ∞]-valued stopping times, for every solution with continuous paths in [0, 1] and the published Itô relation; reason: Lean conventions; the supremum is never a default value
--   - encoding: r and σ̃ are a discount rate and a volatility, with no stated sign → r > 0 and σ̃ > 0; reason: the paper uses both silently (γ needs σ̃ ≠ 0, and r = 0 gives γ = 1); only degenerate cases are excluded
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, Theorem 2, p.21; §4.3.3, p.21; Proposition 5, p.20; (A-7), p.53

import Definitions.Def_SeqExpDiffusion_payoff
import Definitions.Def_SeqExpDiffusion_NonDominated
import Definitions.Def_SeqExpDiffusion_pairPayoff
import Definitions.Def_SeqExpDiffusion_IsTwoActionForm
import Definitions.Def_SeqExpDiffusion_pairForm
import Definitions.Def_SeqExpDiffusion_pairMax
import Definitions.Def_SeqExpDiffusion_IsHatC2
import Definitions.Def_SeqExpDiffusion_IsValueFunction

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- Theorem 2, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.21: the function `Ṽ(δ) = max_{{a_i, a_j} ∈ 𝒜} 𝒢̃_ij(δ)` is in `Ĉ²`. As a result,
`𝒢̃(δ) = Ṽ(δ)`.

Let `𝒜` be finite with at least two actions, with affine non-dominated rewards, `r > 0`, `σ̃ > 0`, and
`G ≥ 0` on `[0, 1]`. There is a family `𝒢̃_ij` (`i ≠ j`) such that
1. each `𝒢̃_ij` is the value function of (12) with the two-action payoff `G̃_ij` (p.21);
2. for every pair with `a_i` the left action (`β i < β j`) and `G̃_ij ≥ 0` on `[0, 1]`, `𝒢̃_ij` is the
   closed form (18) of Proposition 5 on `[0, 1]`;
3. `Ṽ = max_{i ≠ j} 𝒢̃_ij` is in `Ĉ²`;
4. `Ṽ` is the value function `𝒢̃` of (12) with the payoff `G`.

**Formalization Note** Clause 2 records that the `𝒢̃_ij` of the theorem are those of (18), with the
corrected thresholds of `IsTwoActionForm`. The paper assumes `G̃_ij ≥ 0` for every pair "without loss
of generality" (p.19); here only `G ≥ 0` is assumed, and (18) is asserted for the nonnegative pairs,
which are all pairs in the paper's setting. -/
theorem theorem_2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] (α β : ι → ℝ)
    (hnd : NonDominated α β) (r σ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hG : ∀ δ ∈ Icc (0 : ℝ) 1, 0 ≤ payoff α β δ) :
    ∃ v : ι → ι → ℝ → ℝ,
      (∀ i j, i ≠ j → IsValueFunction r σ (pairPayoff α β i j) (v i j)) ∧
      (∀ i j, β i < β j → (∀ δ ∈ Icc (0 : ℝ) 1, 0 ≤ pairPayoff α β i j δ) →
        ∃ a b C₀ C₁ : ℝ, IsTwoActionForm r σ α β i j a b C₀ C₁ ∧
          ∀ δ ∈ Icc (0 : ℝ) 1, v i j δ = pairForm r σ α β i j a b C₀ C₁ δ) ∧
      IsHatC2 (pairMax v) ∧
      IsValueFunction r σ (payoff α β) (pairMax v) := by sorry

end SeqExpDiffusion
