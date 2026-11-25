-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeDual_int_fg_d6bcc96c1a9d
-- name    : P2M_GroundTheory_Heights__Heights_latticeDual_int_fg_d6bcc96c1a9d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:29.107283+00:00
-- url     : https://prove2.me/theorems/095afdad-fb58-416b-a3c4-b6d0bb173b82
-- title:
--   P2 M Ground Theory Heights  Heights lattice Dual int fg d6bcc96c1a9d: P2 M Ground Theory Heights  Heights lattice Dual int fg d6bcc96c1a9d
-- statement:
--   The P2 M Ground Theory Heights  Heights lattice Dual int fg d6bcc96c1a9d construction uses the P2 M Ground Theory Heights  Heights lattice Dual int fg d6bcc96c1a9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PDualBasisExists.lean#L11-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PDualBasisExists.lean#L11-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PDualBasisExists
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

theorem P2M_GroundTheory_Heights__Heights_latticeDual_int_fg_d6bcc96c1a9d {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ((latticeDual F.lattice).restrictScalars ℤ).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«latticeDual_int_fg» := P2M_GroundTheory_Heights__Heights_latticeDual_int_fg_d6bcc96c1a9d
