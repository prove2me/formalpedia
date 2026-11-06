-- Prove2me | Theorems.Thm_RH_Transport_TunedEndpoint_witness_in_domain
-- name    : RH.Transport.TunedEndpoint.witness_in_domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:26:12.836724+00:00
-- url     : https://prove2.me/theorems/8c52dde2-d452-4f59-9688-88d9860e018e
-- title:
--   Tuned Endpoint: witness in domain
-- statement:
--   The Tuned Endpoint construction uses the witness in domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedEndpoint.lean#L1406-L1409
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedEndpoint.lean#L1406-L1409

import Definitions.Def_Transport_Endpoint
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_TunedEndpoint
import Theorems.Thm_RH_Transport_Endpoint_witness_in_domain

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.TunedEndpoint
noncomputable section

theorem RH.Transport.TunedEndpoint.witness_in_domain :
    (1 / 50 : ℝ) ≤ witnessDelta1 ∧ witnessDelta1 ≤ 3 / 4 ∧
    (1 / 50 : ℝ) ≤ witnessDelta2 ∧ witnessDelta2 ≤ 3 / 4 := by sorry
