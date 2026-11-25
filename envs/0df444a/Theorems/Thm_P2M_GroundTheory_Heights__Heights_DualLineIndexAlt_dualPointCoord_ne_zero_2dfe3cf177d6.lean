-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineIndexAlt_dualPointCoord_ne_zero_2dfe3cf177d6
-- name    : P2M_GroundTheory_Heights__Heights_DualLineIndexAlt_dualPointCoord_ne_zero_2dfe3cf177d6
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:08.150335+00:00
-- url     : https://prove2.me/theorems/cae07e1f-b1f1-5218-91fd-33b5fc4fe21e
-- title:
--   P2 M Ground Theory Heights  Heights Dual Line Index Alt dual Point Coord ne zero 2dfe3cf177d6: P2 M Ground Theory Heights  Heights Dual Line Index Alt dual Point Coord ne zero 2dfe3cf177d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Line Index Alt dual Point Coord ne zero 2dfe3cf177d6 construction uses the P2 M Ground Theory Heights  Heights Dual Line Index Alt dual Point Coord ne zero 2dfe3cf177d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineIndex.lean#L84-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineIndex.lean#L84-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineIdealDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIdealIndexPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.DualLineIndexAlt

theorem P2M_GroundTheory_Heights__Heights_DualLineIndexAlt_dualPointCoord_ne_zero_2dfe3cf177d6 {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) {K' : Type} [Field K'] [Algebra K K'] {v : Fin i → K'}
    (hv : v ≠ 0) : dualPointCoord b v ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLineIndexAlt».«dualPointCoord_ne_zero» := P2M_GroundTheory_Heights__Heights_DualLineIndexAlt_dualPointCoord_ne_zero_2dfe3cf177d6
