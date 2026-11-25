-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isRadical_map
-- name    : ReciprocityTheory.AnForm.R.BaseChangeC.isRadical_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:05.043193+00:00
-- url     : https://prove2.me/theorems/a73fa833-59c2-55ce-b9f9-a7b6d08bdbcc
-- title:
--   Base Change C: is Radical map
-- statement:
--   The Base Change C construction uses the is Radical map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCB.lean#L25-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCB.lean#L25-L39

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

theorem ReciprocityTheory.AnForm.R.BaseChangeC.isRadical_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] : (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).IsRadical := by sorry
