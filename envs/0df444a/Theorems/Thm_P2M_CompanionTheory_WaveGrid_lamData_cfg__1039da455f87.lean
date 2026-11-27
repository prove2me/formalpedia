-- Prove2me | Theorems.Thm_P2M_CompanionTheory_WaveGrid_lamData_cfg__1039da455f87
-- name    : P2M_CompanionTheory_WaveGrid_lamData_cfg__1039da455f87
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:41.738234+00:00
-- url     : https://prove2.me/theorems/817b4729-67a6-519e-85dd-7591e9273abd
-- title:
--   P2 M Companion Theory Wave Grid lam Data cfg  1039da455f87: P2 M Companion Theory Wave Grid lam Data cfg  1039da455f87
-- statement:
--   The P2 M Companion Theory Wave Grid lam Data cfg  1039da455f87 construction uses the P2 M Companion Theory Wave Grid lam Data cfg  1039da455f87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L172-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/CfgTie.lean#L172-L181

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset

theorem P2M_CompanionTheory_WaveGrid_lamData_cfg__1039da455f87 :
    LamData (cfgPar cfg₀ 0 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0)) cfg₀.lam 10 (4 * cfg₀.Del) 400 := by sorry

alias «CompanionTheory».«WaveGrid».«lamData_cfg₀» := P2M_CompanionTheory_WaveGrid_lamData_cfg__1039da455f87
