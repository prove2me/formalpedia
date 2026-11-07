-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_exists_large_prime_parameter
-- name    : QEC.Coding.ExpanderCodes.exists_large_prime_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:30:58.735142+00:00
-- url     : https://prove2.me/theorems/671139d0-e882-4f8e-aab9-8e4e3912a4ee
-- title:
--   Expander Codes: exists large prime parameter
-- statement:
--   Arbitrarily large odd prime fields admit the actual nonsquare parameter.
--   The resulting orbit degree is `p + 1`; no graph spectrum is included here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/PrimeFieldParameters.lean#L31-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/PrimeFieldParameters.lean#L31-L41

import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_PrimeFieldParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes

theorem QEC.Coding.ExpanderCodes.exists_large_prime_parameter (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N ≤ p + 1 ∧ 3 ≤ p ∧
      ∃ epsilon : ZMod p, epsilon ≠ 0 ∧ ∀ r : ZMod p, r ^ 2 ≠ epsilon := by sorry
