-- Prove2me | Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_ofFn
-- name    : PermanentRollout.freeAffineCircuitSquareFamily_ofFn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/844ecfe1-3c7c-4804-aa61-048189e0ed31
-- title:
--   PermanentRollout.freeAffineCircuitSquareFamily_ofFn
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.freeAffineCircuitSquareFamily_ofFn
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (output : Fin k → FreeAffineForm (Fin k)) (target : Fin k → ℂ) :
    List.ofFn (freeAffineCircuitSquareFamily circuit output target) =
      (List.ofFn fun j : Fin circuit.program.length =>
        freeAffineCircuitInstructionEquation circuit j) ++
      (List.ofFn fun i : Fin k =>
        freeAffineExtendedForm
          (n := circuit.program.length) (output i) -
          MvPolynomial.C (target i)) := by sorry
