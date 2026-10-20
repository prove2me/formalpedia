-- Prove2me | Theorems.Thm_PermanentRollout_homogeneous_fin_one_eval
-- name    : PermanentRollout.homogeneous_fin_one_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/67bedff0-2399-4afc-9ef7-6a40f1b20186
-- title:
--   PermanentRollout.homogeneous_fin_one_eval
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization

theorem PermanentRollout.homogeneous_fin_one_eval
    {f : MvPolynomial (Fin 1) ℂ} {e : ℕ}
    (hf : f.IsHomogeneous e) (u : Fin 1 → ℂ) :
    MvPolynomial.eval u f =
      u 0 ^ e * MvPolynomial.eval (fun _ : Fin 1 => 1) f := by sorry
