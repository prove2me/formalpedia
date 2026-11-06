-- Prove2me | Theorems.Thm_QEC_Coding_FiniteSymplectic_form_nondegenerate
-- name    : QEC.Coding.FiniteSymplectic.form_nondegenerate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:14.843052+00:00
-- url     : https://prove2.me/theorems/4d9a910c-4f01-427f-a024-0502399e1f78
-- title:
--   Finite Symplectic: form nondegenerate
-- statement:
--   The standard finite-coordinate symplectic form is nondegenerate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Symplectic.lean#L127-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Symplectic.lean#L127-L150

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u v
open QEC.Coding.FiniteSymplectic
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.FiniteSymplectic.form_nondegenerate : (form (F := F) (ι := ι)).Nondegenerate := by sorry
