-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_exists_full_degree_parameter
-- name    : QEC.Coding.ExpanderCodes.exists_full_degree_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:44:15.343282+00:00
-- url     : https://prove2.me/theorems/1c0153bd-21d7-4ecd-af13-fd59f8c21b7f
-- title:
--   Expander Codes: exists full degree parameter
-- statement:
--   An actual generator of a finite extension avoids the two excluded points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSpecialization.lean#L21-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSpecialization.lean#L21-L49

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField

theorem QEC.Coding.ExpanderCodes.exists_full_degree_parameter (p n : ℕ) [Fact p.Prime] (hDegree : 1 < n) :
    ∃ y : GaloisField p n, y ≠ 0 ∧ 1 + y ≠ 0 ∧
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = n ∧
      adjoin (ZMod p) ({y} : Set (GaloisField p n)) = ⊤ := by sorry
