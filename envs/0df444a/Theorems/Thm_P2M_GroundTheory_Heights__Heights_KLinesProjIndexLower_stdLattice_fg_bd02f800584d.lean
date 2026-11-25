-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_fg_bd02f800584d
-- name    : P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_fg_bd02f800584d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:47.325684+00:00
-- url     : https://prove2.me/theorems/ed67ac57-812a-54f0-a977-ad194bc6ed4a
-- title:
--   P2 M Ground Theory Heights  Heights KLines Proj Index Lower std Lattice fg bd02f800584d: P2 M Ground Theory Heights  Heights KLines Proj Index Lower std Lattice fg bd02f800584d
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Proj Index Lower std Lattice fg bd02f800584d construction uses the P2 M Ground Theory Heights  Heights KLines Proj Index Lower std Lattice fg bd02f800584d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProjIndexLower.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesProjIndexLower.lean#L13-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProjIndexLower
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
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.KLinesProjIndexLower

theorem P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_fg_bd02f800584d (K : Type) [Field K] [NumberField K] (k : ℕ) :
    ((stdLattice K k).restrictScalars ℤ).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesProjIndexLower».«stdLattice_fg» := P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_fg_bd02f800584d
