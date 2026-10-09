-- Prove2me | Theorems.Thm_StatComplexityDM_PCIGW_pcigw_dec_tabular
-- name    : StatComplexityDM.PCIGW.pcigw_dec_tabular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:59.323122+00:00
-- url     : https://prove2.me/theorems/54a8d1a2-1745-4194-b1d6-2a267e6490e5
-- title:
--   Proposition 5.6 — PC-IGW certifies dec_γ ≤ 95H³SA/γ
-- statement:
--   Let $\bar M$ be a normalized tabular MDP with $S$ states, $A$ actions, and horizon $H$. Algorithm 4 uses the cover parameter $\eta=\gamma/(21H^2)$ for $\gamma>0$ and returns a normalized distribution $p$ on its distinct cover policies and $\pi_{\bar M}$. For every normalized tabular MDP $M$ in the same class,
--   $$
--   \mathbb E_{\pi\sim p}\!\left[f^M(\pi_M)-f^M(\pi)-\gamma D_H^2(M(\pi),\bar M(\pi))\right]\le\frac{95H^3SA}{\gamma}.
--   $$
--   The bound is uniform in $M$, so this explicit distribution certifies the paper's frequentist decision-estimation coefficient upper bound. Here $M(\pi)$ is the full trajectory law of states, actions, and rewards.
--
--   **Formalization Note** The formal target is the displayed explicit-strategy inequality. State, action, and reward alphabets are finite and nonempty; policies may randomize, rounds use `Fin H`, and the terminal transition is omitted. The formal normalization predicate additionally requires nonnegative stage rewards and the total reward bound on supported suffixes from any state, to support Lemma F.3. The theorem quantifies over all value-maximizing policy selectors and all covers satisfying (56) and (57), with $\lambda$ fixed by normalization.
-- source:
--   arXiv:2112.13487v3, Proposition 5.6, p. 36; proof pp. 36–38

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_Algorithm

namespace StatComplexityDM.PCIGW

/-- Proposition 5.6, p. 36: the explicit PC-IGW distribution certifies
the frequentist DEC bound for every tabular MDP in the class. -/
theorem pcigw_dec_tabular {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H)
    (γ η lam : ℝ) (cover : Fin H → S → A → StatComplexityDM.TabularPS.Policy S A H)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1)
    (hMbar : StatComplexityDM.TabularPS.IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hpiStar : IsOptimalSelector d1 rv piStar)
    (hγ : 0 < γ) (hη : η = γ / (21 * (H : ℝ) ^ 2))
    (halg : IsPCIGW d1 rv Mbar piStar η cover lam) :
    ∀ M : StatComplexityDM.TabularPS.TabMDP S A W H,
      StatComplexityDM.TabularPS.IsTabMDP M → RewardsNormalized d1 rv M →
      (∑ π ∈ pcigwPsi Mbar piStar cover,
        pcigwWeight d1 rv Mbar piStar η lam π *
          (StatComplexityDM.TabularPS.value d1 rv M (piStar M) - StatComplexityDM.TabularPS.value d1 rv M π -
            γ * FoundationsRL.GeneralDM.hellingerSq
              (StatComplexityDM.TabularPS.trajLaw d1 M π) (StatComplexityDM.TabularPS.trajLaw d1 Mbar π))) ≤
        95 * (H : ℝ) ^ 3 * Fintype.card S * Fintype.card A / γ := by sorry

end StatComplexityDM.PCIGW
