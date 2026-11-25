-- Prove2me | Theorems.Thm_P2M_CompanionTheory_WaveGrid_hypType__bc1b63aaa92d
-- name    : P2M_CompanionTheory_WaveGrid_hypType__bc1b63aaa92d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:08:15.545885+00:00
-- url     : https://prove2.me/theorems/cff73551-4ffa-5b52-a8ae-af804abc6976
-- title:
--   P2 M Companion Theory Wave Grid hyp Type  bc1b63aaa92d: P2 M Companion Theory Wave Grid hyp Type  bc1b63aaa92d
-- statement:
--   The P2 M Companion Theory Wave Grid hyp Type  bc1b63aaa92d construction uses the P2 M Companion Theory Wave Grid hyp Type  bc1b63aaa92d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L241-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L241-L267

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

theorem P2M_CompanionTheory_WaveGrid_hypType__bc1b63aaa92d (a : ℤ) (ha : 10 ≤ a) (ha' : a ≤ 40) :
    HypType P₂.k P₂.r lam₂ (fun i => if i = 1 then (a : ℝ) + 1 / 2 else 1 / 2) 41 := by sorry

alias «CompanionTheory».«WaveGrid».«hypType₂» := P2M_CompanionTheory_WaveGrid_hypType__bc1b63aaa92d
