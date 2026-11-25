-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isDomain_tensor_of_isFractionRing
-- name    : ReciprocityTheory.AnForm.R.BaseChangeC.isDomain_tensor_of_isFractionRing
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:11.509209+00:00
-- url     : https://prove2.me/theorems/94c98582-6a89-4d0a-917f-a9d305022640
-- title:
--   Base Change C: is Domain tensor of is Fraction Ring
-- statement:
--   The Base Change C construction uses the is Domain tensor of is Fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCA.lean#L43-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCA.lean#L43-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
variable (ι : Type) (F : Type) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial ι ℚ) F]
  [IsScalarTower ℚ (MvPolynomial ι ℚ) F] [IsFractionRing (MvPolynomial ι ℚ) F]
  (C : Type) [Field C] [Algebra ℚ C]
include ι

theorem ReciprocityTheory.AnForm.R.BaseChangeC.isDomain_tensor_of_isFractionRing : IsDomain (F ⊗[ℚ] C) := by sorry
