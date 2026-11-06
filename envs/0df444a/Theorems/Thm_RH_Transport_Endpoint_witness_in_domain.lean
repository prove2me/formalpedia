-- Prove2me | Theorems.Thm_RH_Transport_Endpoint_witness_in_domain
-- name    : RH.Transport.Endpoint.witness_in_domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:24:00.675205+00:00
-- url     : https://prove2.me/theorems/c6fe4a1d-d4b9-43de-9cb4-b6dd830631d7
-- title:
--   Endpoint: witness in domain
-- statement:
--   The Endpoint construction uses the witness in domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Endpoint.lean#L1272-L1275
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Endpoint.lean#L1272-L1275

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Endpoint
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open RH RH.Transport RH.Transport.Endpoint
noncomputable section

theorem RH.Transport.Endpoint.witness_in_domain :
    (1 / 50 : ℝ) ≤ witnessDelta ∧ witnessDelta ≤ 3 / 4 ∧
      (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 / 2 := by sorry
