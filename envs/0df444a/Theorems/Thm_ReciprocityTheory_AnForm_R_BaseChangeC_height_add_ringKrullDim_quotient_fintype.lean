-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_height_add_ringKrullDim_quotient_fintype
-- name    : ReciprocityTheory.AnForm.R.BaseChangeC.height_add_ringKrullDim_quotient_fintype
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:55.923639+00:00
-- url     : https://prove2.me/theorems/731df631-5fca-452e-af70-790bd3f2918d
-- title:
--   Base Change C: height add ring Krull Dim quotient fintype
-- statement:
--   The Base Change C construction uses the height add ring Krull Dim quotient fintype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCB.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCB.lean#L92-L101

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

theorem ReciprocityTheory.AnForm.R.BaseChangeC.height_add_ringKrullDim_quotient_fintype (k : Type) [Field k]
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ P) = Fintype.card σ := by sorry
