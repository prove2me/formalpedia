-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_inv_line
-- name    : PositivityTheory.Rg.Sw.SP.inv_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:51.099951+00:00
-- url     : https://prove2.me/theorems/293f111f-6154-4330-bb9e-67fe1b8c18b5
-- title:
--   SP: inv line
-- statement:
--   The SP construction uses the inv line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeH.lean#L24-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeH.lean#L24-L61

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.inv_line (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0)
    (hdiff : ∀ a d, DifferentiableAt ℂ (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0) (a d : Fin n) :
    HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) ((-(M0⁻¹ * A * M0⁻¹)) a d) 0 := by sorry
