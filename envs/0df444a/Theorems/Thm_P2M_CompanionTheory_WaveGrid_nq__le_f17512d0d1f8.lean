-- Prove2me | Theorems.Thm_P2M_CompanionTheory_WaveGrid_nq__le_f17512d0d1f8
-- name    : P2M_CompanionTheory_WaveGrid_nq__le_f17512d0d1f8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:35.648812+00:00
-- url     : https://prove2.me/theorems/9a5dffe0-e600-5667-b8b8-eefb2095a264
-- title:
--   P2 M Companion Theory Wave Grid nq  le f17512d0d1f8: P2 M Companion Theory Wave Grid nq  le f17512d0d1f8
-- statement:
--   The P2 M Companion Theory Wave Grid nq  le f17512d0d1f8 construction uses the P2 M Companion Theory Wave Grid nq  le f17512d0d1f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L139-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselWaveGrids/PStarTie.lean#L139-L166

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

theorem P2M_CompanionTheory_WaveGrid_nq__le_f17512d0d1f8 (P : M.Par) (b CT : ℝ) (hb : 1 ≤ b) (hCT : 0 ≤ CT)
    (hTT : b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T') :
    nqΛ P b ≤ b ^ ((5 + CT) * ((2 * P.r + 2 : ℕ) : ℝ)) := by sorry

alias «CompanionTheory».«WaveGrid».«nqΛ_le» := P2M_CompanionTheory_WaveGrid_nq__le_f17512d0d1f8
