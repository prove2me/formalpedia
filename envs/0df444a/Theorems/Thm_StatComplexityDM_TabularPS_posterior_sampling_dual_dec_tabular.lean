-- Prove2me | Theorems.Thm_StatComplexityDM_TabularPS_posterior_sampling_dual_dec_tabular
-- name    : StatComplexityDM.TabularPS.posterior_sampling_dual_dec_tabular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:09.163798+00:00
-- url     : https://prove2.me/theorems/56b31e3c-793b-4a48-b32e-564820765e00
-- title:
--   Proposition 5.4 — posterior sampling bounds the dual DEC by 26H²SA/γ
-- statement:
--   Consider a horizon-$H$ tabular reinforcement-learning class with $S$ states, $A$ actions, a shared initial law, and total episode reward in $[0,1]$. Let $\mu$ be a finitely supported prior on the class, let $\pi_M$ maximize the value for each model, and let $\bar M$ be a normalized reference model in the same tabular class. If $p$ is the law of $\pi_{M'}$ for an independent draw $M'\sim\mu$, then for every $\gamma>0$,
--   $$
--   \mathbb E_{M\sim\mu,\pi\sim p}
--     [f^M(\pi_M)-f^M(\pi)-\gamma D_H^2(M(\pi),\bar M(\pi))]
--     \le\frac{26H^2SA}{\gamma}.
--   $$
--   Thus posterior sampling supplies the advertised upper bound on the dual decision-estimation objective for every finitely supported prior.
--
--   **Formalization Note** Policies remain randomized. The expectations are a double finite sum over independent model draws. $M(\pi)$ is the full trajectory law, not a one-step kernel. The reference model is in the tabular normalized class, matching the case actually proved in §5.2.1; the printed proposition also mentions external reference models. Finite reward, state, and action alphabets are used. Reward normalization includes §5.2's reward space $[0,1]$ and the almost-sure bound $\sum_h r_h\in[0,1]$ under every policy.
-- source:
--   arXiv:2112.13487v3, Proposition 5.4, p. 33; proof pp. 33–35

import Mathlib
import Definitions.Def_StatComplexityDM_TabularPS_MDP

namespace StatComplexityDM.TabularPS

/-- Proposition 5.4, p. 33, in the case of a reference model in the tabular
model class, as proved in §5.2.1. -/
theorem posterior_sampling_dual_dec_tabular {S A W I : Type*}
    [Fintype S] [Fintype A] [Fintype W] [Fintype I]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Ms : I → TabMDP S A W H) (w : I → ℝ)
    (Mbar : TabMDP S A W H)
    (piStar : TabMDP S A W H → Policy S A H) (γ : ℝ)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1) (hw : StatComplexityDM.LowerBound.IsDist w)
    (hMs : ∀ i, IsTabMDP (Ms i) ∧ RewardsNormalized d1 rv (Ms i))
    (hMbar : IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hpiStar : ∀ M, IsTabMDP M → RewardsNormalized d1 rv M →
      IsPolicy (piStar M) ∧
        ∀ π, IsPolicy π → value d1 rv M π ≤ value d1 rv M (piStar M))
    (hγ : 0 < γ) :
    ∑ i, w i * ∑ j, w j *
      (value d1 rv (Ms i) (piStar (Ms i)) -
        value d1 rv (Ms i) (piStar (Ms j)) -
        γ * FoundationsRL.GeneralDM.hellingerSq
          (trajLaw d1 (Ms i) (piStar (Ms j)))
          (trajLaw d1 Mbar (piStar (Ms j)))) ≤
      26 * (H : ℝ) ^ 2 * Fintype.card S * Fintype.card A / γ := by sorry

end StatComplexityDM.TabularPS
