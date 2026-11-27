-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TraceExpSmul_trace_mul_exp_smul__ab68fdf078d0
-- name    : P2M_GlobalTheory_TraceExpSmul_trace_mul_exp_smul__ab68fdf078d0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:44.023687+00:00
-- url     : https://prove2.me/theorems/4dd67ba0-9f82-5d3b-9b3b-8918ee21e9b1
-- title:
--   P2 M Global Theory Trace Exp Smul trace mul exp smul  ab68fdf078d0: P2 M Global Theory Trace Exp Smul trace mul exp smul  ab68fdf078d0
-- statement:
--   The P2 M Global Theory Trace Exp Smul trace mul exp smul  ab68fdf078d0 construction uses the P2 M Global Theory Trace Exp Smul trace mul exp smul  ab68fdf078d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TraceRMulPowEqZero.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TraceRMulPowEqZero.lean#L39-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TraceRMulPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceExpSmul
open Finset
variable {K : Type*} {n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem P2M_GlobalTheory_TraceExpSmul_trace_mul_exp_smul__ab68fdf078d0.{u, v} : ∀ {K : Type u} {n : Type v} [inst : Field K] [inst_1 : CharZero K] [inst_2 : Fintype n] [inst_3 : DecidableEq n] {R N : Matrix n n K}, IsNilpotent N → ∀ {d : K}, N * R = d • (R * N) → ∀ (s : K), Matrix.trace (R * IsNilpotent.exp (s • N)) = Matrix.trace R := by sorry

alias «GlobalTheory».«TraceExpSmul».«trace_mul_exp_smul».«» := P2M_GlobalTheory_TraceExpSmul_trace_mul_exp_smul__ab68fdf078d0
