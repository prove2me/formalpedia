-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_flat_mvPolynomial_rat_complex
-- name    : ReciprocityTheory.AnForm.R.BaseChangeC.flat_mvPolynomial_rat_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:56.472262+00:00
-- url     : https://prove2.me/theorems/3d59cfea-c11f-4377-9dbb-dacd3f1717e0
-- title:
--   Base Change C: flat mv Polynomial rat complex
-- statement:
--   The Base Change C construction uses the flat mv Polynomial rat complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCB.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCB.lean#L47-L50

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
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
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem ReciprocityTheory.AnForm.R.BaseChangeC.flat_mvPolynomial_rat_complex :
    Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) := by sorry
