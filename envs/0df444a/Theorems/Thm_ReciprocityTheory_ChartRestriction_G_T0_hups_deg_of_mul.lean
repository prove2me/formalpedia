-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_deg_of_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hups_deg_of_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-27T05:36:33.964393+00:00
-- url     : https://prove2.me/theorems/431612f0-bb1f-4d69-93d0-c644b957a5de
-- title:
--   T0: hups deg of mul
-- statement:
--   The T0 construction uses the hups deg of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsTwCoeffCoeff.lean#L88-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsTwCoeffCoeff.lean#L88-L112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0

theorem ReciprocityTheory.ChartRestriction.G.T0.hups_deg_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} {u n : ℕ} {sF : σ →₀ ℕ} (hsF : sF ∈ F.support)
    (hFu : hupsWt w sF = u)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s ≤ n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + u ≤ n := by sorry
