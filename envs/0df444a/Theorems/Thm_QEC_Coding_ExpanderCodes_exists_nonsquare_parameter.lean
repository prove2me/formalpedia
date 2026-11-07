-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_exists_nonsquare_parameter
-- name    : QEC.Coding.ExpanderCodes.exists_nonsquare_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:06.56937+00:00
-- url     : https://prove2.me/theorems/98591167-3ec5-4142-8d29-b99d6684696c
-- title:
--   Expander Codes: exists nonsquare parameter
-- statement:
--   A finite field of odd characteristic has a nonzero quadratic parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/PrimeFieldParameters.lean#L19-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/PrimeFieldParameters.lean#L19-L27

import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_PrimeFieldParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes

theorem QEC.Coding.ExpanderCodes.exists_nonsquare_parameter (F : Type*) [Field F] [Finite F]
    (hTwo : ringChar F ≠ 2) :
    ∃ epsilon : F, epsilon ≠ 0 ∧ ∀ r : F, r ^ 2 ≠ epsilon := by sorry
