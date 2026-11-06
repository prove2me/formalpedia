-- Prove2me | Theorems.Thm_QEC_Coding_FiniteSymplectic_form_isAlt
-- name    : QEC.Coding.FiniteSymplectic.form_isAlt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:13.140082+00:00
-- url     : https://prove2.me/theorems/d8017eac-bed1-4c78-8e0e-4dd602efaa06
-- title:
--   Finite Symplectic: form is Alt
-- statement:
--   The standard symplectic form is alternating.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Symplectic.lean#L118-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Symplectic.lean#L118-L124

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

theorem QEC.Coding.FiniteSymplectic.form_isAlt : (form (F := F) (ι := ι)).IsAlt := by sorry
