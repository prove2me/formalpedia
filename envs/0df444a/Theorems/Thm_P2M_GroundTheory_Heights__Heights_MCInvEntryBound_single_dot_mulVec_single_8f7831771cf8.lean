-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryBound_single_dot_mulVec_single_8f7831771cf8
-- name    : P2M_GroundTheory_Heights__Heights_MCInvEntryBound_single_dot_mulVec_single_8f7831771cf8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:30.122931+00:00
-- url     : https://prove2.me/theorems/c1742d92-f02a-4bb4-b505-e08c11db05ff
-- title:
--   P2 M Ground Theory Heights  Heights MCInv Entry Bound single dot mul Vec single 8f7831771cf8: P2 M Ground Theory Heights  Heights MCInv Entry Bound single dot mul Vec single 8f7831771cf8
-- statement:
--   The P2 M Ground Theory Heights  Heights MCInv Entry Bound single dot mul Vec single 8f7831771cf8 construction uses the P2 M Ground Theory Heights  Heights MCInv Entry Bound single dot mul Vec single 8f7831771cf8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryBound.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryBound.lean#L14-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryBound
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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCInvEntryBound

theorem P2M_GroundTheory_Heights__Heights_MCInvEntryBound_single_dot_mulVec_single_8f7831771cf8 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (j l : ι) : Pi.single j (1 : ℝ) ⬝ᵥ (A *ᵥ Pi.single l 1) = A j l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCInvEntryBound».«single_dot_mulVec_single» := P2M_GroundTheory_Heights__Heights_MCInvEntryBound_single_dot_mulVec_single_8f7831771cf8
