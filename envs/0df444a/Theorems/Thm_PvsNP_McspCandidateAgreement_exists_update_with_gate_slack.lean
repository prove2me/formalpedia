-- Prove2me | Theorems.Thm_PvsNP_McspCandidateAgreement_exists_update_with_gate_slack
-- name    : PvsNP.McspCandidateAgreement.exists_update_with_gate_slack
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T05:55:32.0149+00:00
-- url     : https://prove2.me/theorems/7592a8aa-c07f-4ea1-98f8-4545e3a7a07d
-- title:
--   Linear gate slack suffices for any truth-table prefix extension
-- statement:
--   For a native circuit on n inputs and any binary address, one can retain every earlier truth-table bit and prescribe the value at that address. A budget that allows the old number of gates plus n+2 gates for true or n+3 gates for false is enough.
-- source:
--   Direct gate-list comparison against the binary cut.

import Definitions.Def_NativeCircuitExtensionSemantics
set_option autoImplicit false
open PvsNP PvsNP.SuccinctCircuits PvsNP.McspCandidateAgreement

theorem PvsNP.McspCandidateAgreement.exists_update_with_gate_slack {n : ℕ} (old : List Gate) (cut : Fin (2^n)) (b : Bool) (s : ℕ)
    (slack : old.length+(n+1)+(if b then 1 else 2) ≤ s) :
    ∃ candidate, candidate.length ≤ s ∧ validUpdate old candidate cut b := by sorry
