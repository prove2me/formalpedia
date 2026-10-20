-- Prove2me | Theorems.Thm_P2M_GapCVP_ThreeCNFReduction_sourceVariable_ne_paddingVariable__063b26f09f58
-- name    : P2M_GapCVP_ThreeCNFReduction_sourceVariable_ne_paddingVariable__063b26f09f58
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/9ce12263-b1fe-4aac-8dcf-aff28e69a41f
-- title:
--   P2M_GapCVP_ThreeCNFReduction_sourceVariable_ne_paddingVariable__063b26f09f58
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | GapCVP | external Lean 4.33.1 validation; bundle SHA256 48b1efd821d2a3e34fadc0f98ff0604b418a7647736e5b368a2e5f6364a2fcb0

import Mathlib
import Definitions.Def_GapCVP
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL

theorem P2M_GapCVP_ThreeCNFReduction_sourceVariable_ne_paddingVariable__063b26f09f58 {T S : ℕ}
    (v : Variable T S) :
    sourceVariable v ≠ paddingVariable₀ := by sorry

alias «GapCVP».«ThreeCNFReduction».«sourceVariable_ne_paddingVariable₀» := P2M_GapCVP_ThreeCNFReduction_sourceVariable_ne_paddingVariable__063b26f09f58
