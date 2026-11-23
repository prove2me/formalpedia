-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitaryFrames_col_mul__08ccc1f94cd1
-- name    : P2M_GlobalTheory_UnitaryFrames_col_mul__08ccc1f94cd1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:51.549261+00:00
-- url     : https://prove2.me/theorems/73409954-9b3b-42cd-871e-311c147561ae
-- title:
--   P2 M Global Theory Unitary Frames col mul  08ccc1f94cd1: P2 M Global Theory Unitary Frames col mul  08ccc1f94cd1
-- statement:
--   The P2 M Global Theory Unitary Frames col mul  08ccc1f94cd1 construction uses the P2 M Global Theory Unitary Frames col mul  08ccc1f94cd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetNeZeroOfIsOrth.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetNeZeroOfIsOrth.lean#L36-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.UnitaryFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem P2M_GlobalTheory_UnitaryFrames_col_mul__08ccc1f94cd1 {r : ℕ} (g P : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (g * P) a = g *ᵥ col P a := by sorry

alias «GlobalTheory».«UnitaryFrames».«col_mul'» := P2M_GlobalTheory_UnitaryFrames_col_mul__08ccc1f94cd1
