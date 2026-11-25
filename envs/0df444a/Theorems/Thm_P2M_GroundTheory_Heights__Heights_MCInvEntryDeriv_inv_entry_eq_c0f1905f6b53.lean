-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_inv_entry_eq_c0f1905f6b53
-- name    : P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_inv_entry_eq_c0f1905f6b53
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:05.080071+00:00
-- url     : https://prove2.me/theorems/d929710f-2a73-49d2-91d7-7e4b3c9b8ec3
-- title:
--   P2 M Ground Theory Heights  Heights MCInv Entry Deriv inv entry eq c0f1905f6b53: P2 M Ground Theory Heights  Heights MCInv Entry Deriv inv entry eq c0f1905f6b53
-- statement:
--   The P2 M Ground Theory Heights  Heights MCInv Entry Deriv inv entry eq c0f1905f6b53 construction uses the P2 M Ground Theory Heights  Heights MCInv Entry Deriv inv entry eq c0f1905f6b53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryDeriv.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryDeriv.lean#L23-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryDeriv
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
open Matrix Topology
open GroundTheory.Heights₂.Heights.MCInvEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℕ}

theorem P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_inv_entry_eq_c0f1905f6b53 (A : Matrix (Fin g) (Fin g) ℝ) (j l : Fin g) :
    A⁻¹ j l = (A.det)⁻¹ * (A.updateRow l (Pi.single j 1)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCInvEntryDeriv».«inv_entry_eq» := P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_inv_entry_eq_c0f1905f6b53
