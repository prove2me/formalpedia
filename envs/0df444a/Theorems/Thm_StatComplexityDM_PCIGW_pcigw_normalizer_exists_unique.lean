-- Prove2me | Theorems.Thm_StatComplexityDM_PCIGW_pcigw_normalizer_exists_unique
-- name    : StatComplexityDM.PCIGW.pcigw_normalizer_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:48.04759+00:00
-- url     : https://prove2.me/theorems/86d9cf78-0095-4b18-8174-5e8691ce82dc
-- title:
--   Proposition 5.7 — unique PC-IGW normalizer in [1, 2HSA]
-- statement:
--   For Algorithm 4's policy cover at exploration rate $\eta>0$, let $\Psi\cup\{\pi_{\bar M}\}$ be its finite set of distinct policies and set $p_\lambda(\pi)=1/(\lambda+\eta(f^{\bar M}(\pi_{\bar M})-f^{\bar M}(\pi)))$. There is exactly one positive $\lambda$ for which $p_\lambda$ sums to one, and it satisfies
--   $$
--   1\le\lambda\le 2HSA.
--   $$
--   Thus the policy weights in Algorithm 4 are well-defined and normalized. The result uses a genuine finite state/action model, a valid initial law, a value-maximizing selector, and a cover obeying (56).
--
--   **Formalization Note** The support is a set, so duplicates do not contribute twice. The alphabets are finite and nonempty, and $H\ge1$.
-- source:
--   arXiv:2112.13487v3, Proposition 5.7, p. 36

import Mathlib
import Definitions.Def_StatComplexityDM_PCIGW_Algorithm

namespace StatComplexityDM.PCIGW

/-- Proposition 5.7, p. 36: the normalizer is unique among all positive
choices, and its StatComplexityDM.TabularPS.value is in the paper's interval. -/
theorem pcigw_normalizer_exists_unique {S A W : Type*}
    [Fintype S] [Fintype A] [Fintype W]
    [Nonempty S] [Nonempty A] [Nonempty W]
    (H : ℕ) (hH : 1 ≤ H) (d1 : S → ℝ) (rv : W → ℝ)
    (Mbar : StatComplexityDM.TabularPS.TabMDP S A W H)
    (piStar : StatComplexityDM.TabularPS.TabMDP S A W H → StatComplexityDM.TabularPS.Policy S A H)
    (η : ℝ) (cover : Fin H → S → A → StatComplexityDM.TabularPS.Policy S A H)
    (hd1 : StatComplexityDM.LowerBound.IsDist d1)
    (hMbar : StatComplexityDM.TabularPS.IsTabMDP Mbar ∧ RewardsNormalized d1 rv Mbar)
    (hpiStar : IsOptimalSelector d1 rv piStar)
    (hη : 0 < η) (hcover : IsPCIGWCover d1 rv Mbar piStar η cover) :
    (∃! lam : ℝ, 0 < lam ∧
      ∑ π ∈ pcigwPsi Mbar piStar cover,
        pcigwWeight d1 rv Mbar piStar η lam π = 1) ∧
    ∀ lam : ℝ, 0 < lam →
      (∑ π ∈ pcigwPsi Mbar piStar cover,
        pcigwWeight d1 rv Mbar piStar η lam π) = 1 →
      1 ≤ lam ∧ lam ≤ 2 * (H : ℝ) * Fintype.card S * Fintype.card A := by sorry

end StatComplexityDM.PCIGW
