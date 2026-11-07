-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_exists_square_ratio_generator
-- name    : QEC.Coding.ExpanderCodes.exists_square_ratio_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:46:34.445234+00:00
-- url     : https://prove2.me/theorems/88cedfaa-9cb6-48cf-b0ba-9d906002787a
-- title:
--   Expander Codes: exists square ratio generator
-- statement:
--   An actual primitive field point with square ratio, obtained by a rational substitution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSquareParameters.lean#L73-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSquareParameters.lean#L73-L110

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField

theorem QEC.Coding.ExpanderCodes.exists_square_ratio_generator {F K : Type*} [Field F] [Field K]
    [Finite K] [Algebra F K] (hCard : 3 < Nat.card K) :
    ∃ y t : K, y ≠ 0 ∧ 1 + y ≠ 0 ∧ t ≠ 0 ∧
      t ^ 2 = y / (1 + y) ∧ adjoin F ({y} : Set K) = ⊤ := by sorry
