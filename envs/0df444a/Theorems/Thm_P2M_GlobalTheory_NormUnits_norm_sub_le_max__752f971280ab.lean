-- Prove2me | Theorems.Thm_P2M_GlobalTheory_NormUnits_norm_sub_le_max__752f971280ab
-- name    : P2M_GlobalTheory_NormUnits_norm_sub_le_max__752f971280ab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:57.873844+00:00
-- url     : https://prove2.me/theorems/39b1523c-1762-4159-be89-22f608044b62
-- title:
--   P2 M Global Theory Norm Units norm sub le max  752f971280ab: P2 M Global Theory Norm Units norm sub le max  752f971280ab
-- statement:
--   The P2 M Global Theory Norm Units norm sub le max  752f971280ab construction uses the P2 M Global Theory Norm Units norm sub le max  752f971280ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadratic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.NormUnits

theorem P2M_GlobalTheory_NormUnits_norm_sub_le_max__752f971280ab {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by sorry

alias «GlobalTheory».«NormUnits».«norm_sub_le_max'» := P2M_GlobalTheory_NormUnits_norm_sub_le_max__752f971280ab
