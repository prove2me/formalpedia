-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_hom_of_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hups_hom_of_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T05:35:30.31829+00:00
-- url     : https://prove2.me/theorems/7c0a8e6b-53e7-4a90-b66b-1c4907c00faa
-- title:
--   T0: hups hom of mul
-- statement:
--   The T0 construction uses the hups hom of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsTwCoeffCoeff.lean#L70-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HupsTwCoeffCoeff.lean#L70-L86

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

theorem ReciprocityTheory.ChartRestriction.G.T0.hups_hom_of_mul {σ R : Type*} [CommRing R] [IsDomain R] (w : σ → ℕ)
    {F P : MvPolynomial σ R} (hF : F ≠ 0) {a n : ℕ} (hFa : ∀ s ∈ F.support, hupsWt w s = a)
    (hFP : ∀ s ∈ (F * P).support, hupsWt w s = n) {s0 : σ →₀ ℕ} (hs0 : s0 ∈ P.support) :
    hupsWt w s0 + a = n := by sorry
