-- Prove2me | Theorems.Thm_P2M_GlobalTheory_g__cube_sub_g__sq_ne_zero_9f5991ca482c
-- name    : P2M_GlobalTheory_g__cube_sub_g__sq_ne_zero_9f5991ca482c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:18.607286+00:00
-- url     : https://prove2.me/theorems/f3127247-697c-4ba0-a732-36d3a01b73fe
-- title:
--   P2 M Global Theory g  cube sub g  sq ne zero 9f5991ca482c: P2 M Global Theory g  cube sub g  sq ne zero 9f5991ca482c
-- statement:
--   The P2 M Global Theory g  cube sub g  sq ne zero 9f5991ca482c construction uses the P2 M Global Theory g  cube sub g  sq ne zero 9f5991ca482c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeDeterminedByInvariants.lean#L44-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology Real UpperHalfPlane
noncomputable section
open GlobalTheory

theorem P2M_GlobalTheory_g__cube_sub_g__sq_ne_zero_9f5991ca482c (L : PeriodPair) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by sorry

alias «GlobalTheory».«g₂_cube_sub_g₃_sq_ne_zero» := P2M_GlobalTheory_g__cube_sub_g__sq_ne_zero_9f5991ca482c
