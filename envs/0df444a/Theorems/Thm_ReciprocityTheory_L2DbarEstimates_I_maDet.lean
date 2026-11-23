-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_maDet
-- name    : ReciprocityTheory.L2DbarEstimates.I.maDet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:14.97796+00:00
-- url     : https://prove2.me/theorems/5732de67-bfa9-426e-bbc0-ade8637acd83
-- title:
--   I: ma Det
-- statement:
--   The I construction uses the ma Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetMonoDetOneAdd.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetMonoDetOneAdd.lean#L9-L10

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_Lemmata_DetMonotoneStarMulSelf_OneLeReDetOneAdd
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open Matrix
open scoped ComplexOrder MatrixOrder

theorem ReciprocityTheory.L2DbarEstimates.I.maDet (n : ℕ) : DetMonoStatement n := by sorry
