-- Prove2me | Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
-- name    : QEC.Coding.FiniteSymplectic.form_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:01.035214+00:00
-- url     : https://prove2.me/theorems/1b8297f8-ff63-486f-bab2-6772d50f3198
-- title:
--   Finite Symplectic: form apply
-- statement:
--   The Finite Symplectic construction uses the form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Symplectic.lean#L114-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Symplectic.lean#L114-L115

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

theorem QEC.Coding.FiniteSymplectic.form_apply (a b : SymplecticVector F ι) :
    form a b = symplecticForm a b := by sorry

attribute [defeq] QEC.Coding.FiniteSymplectic.form_apply
