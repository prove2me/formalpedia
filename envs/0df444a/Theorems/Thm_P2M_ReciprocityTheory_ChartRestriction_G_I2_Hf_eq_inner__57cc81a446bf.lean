-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_eq_inner__57cc81a446bf
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_eq_inner__57cc81a446bf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:35.407033+00:00
-- url     : https://prove2.me/theorems/4c19b5aa-0cff-4780-a170-3c382dbd05ce
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 Hf eq inner  57cc81a446bf: P2 M Reciprocity Theory Chart Restriction G I2 Hf eq inner  57cc81a446bf
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 Hf eq inner  57cc81a446bf construction uses the P2 M Reciprocity Theory Chart Restriction G I2 Hf eq inner  57cc81a446bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfEqInner.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfEqInner.lean#L104-L105

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_eq_inner__57cc81a446bf {ι : Type} [Fintype ι] (w v : EuclideanSpace ℂ ι) : Hf w v = inner ℂ v w := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«Hf_eq_inner'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_eq_inner__57cc81a446bf
