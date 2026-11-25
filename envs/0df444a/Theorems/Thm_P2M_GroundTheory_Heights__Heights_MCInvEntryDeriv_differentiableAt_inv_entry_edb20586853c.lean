-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_inv_entry_edb20586853c
-- name    : P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_inv_entry_edb20586853c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:30.733833+00:00
-- url     : https://prove2.me/theorems/87942c0c-01f6-4a80-b2ce-73d93e9c7090
-- title:
--   P2 M Ground Theory Heights  Heights MCInv Entry Deriv differentiable At inv entry edb20586853c: P2 M Ground Theory Heights  Heights MCInv Entry Deriv differentiable At inv entry edb20586853c
-- statement:
--   The P2 M Ground Theory Heights  Heights MCInv Entry Deriv differentiable At inv entry edb20586853c construction uses the P2 M Ground Theory Heights  Heights MCInv Entry Deriv differentiable At inv entry edb20586853c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryDeriv.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PInvEntryDeriv.lean#L27-L35

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

theorem P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_inv_entry_edb20586853c {Y : E → Matrix (Fin g) (Fin g) ℝ} {p : E}
    (hY : ∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p) (hdet : (Y p).det ≠ 0) (j l : Fin g) :
    DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCInvEntryDeriv».«differentiableAt_inv_entry» := P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_differentiableAt_inv_entry_edb20586853c
