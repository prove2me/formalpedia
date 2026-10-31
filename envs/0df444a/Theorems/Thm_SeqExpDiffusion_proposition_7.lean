-- Prove2me | Theorems.Thm_SeqExpDiffusion_proposition_7
-- name    : SeqExpDiffusion.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:24.574338+00:00
-- url     : https://prove2.me/theorems/44da07dd-4ab5-4143-b6e2-63d8c9851c3c
-- title:
--   Proposition 7 — $\tilde V\ge G$ and the second and third QVI conditions off a finite set (corrected: squared ℋ)
-- statement:
--   Let $\mathscr A$ be a finite set of at least two actions with affine, non-dominated rewards, $r>0$, $\tilde\sigma>0$, and $G\ge0$ on $[0,1]$. For every pair $i\ne j$ let $\tilde{\mathcal G}_{ij}$ be the value function of (12) with payoff $\tilde G_{ij}$, and let $\tilde V=\max_{i\ne j}\tilde{\mathcal G}_{ij}$. Then
--
--   1. $\tilde V(\delta)\ge G(\delta)$ for all $\delta\in[0,1]$;
--   2. there is a finite set $N_{\tilde V}\subseteq[0,1]$ such that for all $\delta\in[0,1]\setminus N_{\tilde V}$ the second derivative $\tilde V''(\delta)$ exists and
--   $$\mathcal H\tilde V(\delta)\le0\qquad\text{and}\qquad\big(\tilde V(\delta)-G(\delta)\big)\,\mathcal H\tilde V(\delta)=0.$$
--
--   Together with Theorem 2's regularity this lets the verification theorem identify $\tilde V$ as the value.
--
--   **Formalization Note** "The second derivative exists" means that $\tilde V$ is differentiable near $\delta$ and its derivative is differentiable at $\delta$, derivatives taken within $[0,1]$.
--
--   Differences from the source:
--   - correction: ℋf = ½ σ̃ δ(1−δ) f″ − r f (display (14), p.18) → ℋf = ½ (σ̃ δ(1−δ))² f″ − r f; reason: the printed operator is not the generator of (12); e.g. for σ̃ = 2, r = 1 the closed form (18) does not solve the printed ℋu = 0 (the ratio δ(1−δ)φ₁″/φ₁ of φ₁ = (1−δ)^{1−γ}δ^γ is 2.38 at δ = 0.3 and 2.08 at δ = 0.6), while it solves the squared one; the page itself uses the square on pp.19, 50, 52
--   - generalization: G̃_ij ≥ 0 on [0, 1] for every pair, "without loss of generality" (p.19), with 𝒢̃_ij the closed form (18) → only G ≥ 0 on [0, 1], with 𝒢̃_ij the value function of each two-action problem; reason: the closed form is that value function for nonnegative pairs (Proposition 5, p.21), so the statement specializes to the page; the printed assumption is not without loss (Figure 4's data R₁ = 6 − 30δ, R₂ = 4 − 5δ has G̃₁₂(1) = −1)
--   - reading: ℋṼ(δ) for δ ∉ N_Ṽ → the second derivative of Ṽ exists at δ, and ℋṼ(δ) is evaluated there; reason: ℋ is defined only where f″ exists ((14), p.18)
--   - encoding: |𝒜| ≥ 2 and the maximum over unordered pairs {a_i, a_j} → a nontrivial finite type and the maximum over ordered pairs i ≠ j; reason: both orders of a pair carry the same problem
--   - generalization: stopping times of the filtration 𝔽 of the experimentation history (p.8) → every probability space and every filtration for which the driving motion is Brownian; reason: the paper's setting is one instance, so the statement specializes to it
--   - reading: (12) is silent on the event τ = ∞ → the reward is 0 on {τ = ∞}; reason: the payoffs are bounded, so this changes no supremum relative to finite stopping times
--   - encoding: r and σ̃ are a discount rate and a volatility, with no stated sign → r > 0 and σ̃ > 0; reason: the paper uses both silently (γ needs σ̃ ≠ 0, and r = 0 gives γ = 1); only degenerate cases are excluded
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, Proposition 7, p.21; proof, pp.52–53

import Definitions.Def_SeqExpDiffusion_payoff
import Definitions.Def_SeqExpDiffusion_NonDominated
import Definitions.Def_SeqExpDiffusion_pairPayoff
import Definitions.Def_SeqExpDiffusion_pairMax
import Definitions.Def_SeqExpDiffusion_genH
import Definitions.Def_SeqExpDiffusion_IsValueFunction

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- Proposition 7, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.21: for all `δ ∈ [0, 1]`, `Ṽ(δ) ≥ G̃(δ)`. Also, there exists a finite set
`N_Ṽ ⊆ [0, 1]` such that `ℋṼ(δ) ≤ 0` and `(Ṽ(δ) − G̃(δ)) ℋṼ(δ) = 0` for all `δ ∈ [0, 1] \ N_Ṽ`.

Here `G̃ = G` is the payoff (1) of a finite action set with at least two actions, affine
non-dominated rewards and `G ≥ 0` on `[0, 1]`; `Ṽ = max_{i ≠ j} 𝒢̃_ij`, where each `𝒢̃_ij` is the value
function of (12) with the two-action payoff `G̃_ij`.

**Formalization Note** Off `N_Ṽ` the second derivative of `Ṽ` exists (as a derivative within `[0, 1]`
of a derivative that exists near `δ`), so `ℋṼ(δ)` is not a junk value. `ℋ` is the corrected (14). The
paper's `G̃_ij ≥ 0` for every pair (p.19) is replaced by `G ≥ 0`. -/
theorem proposition_7 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] (α β : ι → ℝ)
    (hnd : NonDominated α β) (r σ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hG : ∀ δ ∈ Icc (0 : ℝ) 1, 0 ≤ payoff α β δ) (v : ι → ι → ℝ → ℝ)
    (hv : ∀ i j, i ≠ j → IsValueFunction r σ (pairPayoff α β i j) (v i j)) :
    (∀ δ ∈ Icc (0 : ℝ) 1, payoff α β δ ≤ pairMax v δ) ∧
    ∃ N : Set ℝ, N.Finite ∧ N ⊆ Icc 0 1 ∧ ∀ δ ∈ Icc (0 : ℝ) 1 \ N,
      (∀ᶠ x in nhdsWithin δ (Icc 0 1), DifferentiableWithinAt ℝ (pairMax v) (Icc 0 1) x) ∧
      DifferentiableWithinAt ℝ (derivWithin (pairMax v) (Icc 0 1)) (Icc 0 1) δ ∧
      genH r σ (pairMax v) δ ≤ 0 ∧ (pairMax v δ - payoff α β δ) * genH r σ (pairMax v) δ = 0 := by sorry

end SeqExpDiffusion
