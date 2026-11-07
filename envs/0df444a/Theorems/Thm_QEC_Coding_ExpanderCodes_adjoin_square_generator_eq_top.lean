-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_adjoin_square_generator_eq_top
-- name    : QEC.Coding.ExpanderCodes.adjoin_square_generator_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:46:23.665676+00:00
-- url     : https://prove2.me/theorems/849f4d6d-7d46-4f81-923f-2843da722033
-- title:
--   Expander Codes: adjoin square generator eq top
-- statement:
--   The square of a multiplicative generator still generates the entire finite field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSquareParameters.lean#L20-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSquareParameters.lean#L20-L70

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField

theorem QEC.Coding.ExpanderCodes.adjoin_square_generator_eq_top {F K : Type*} [Field F] [Field K]
    [Finite K] [Algebra F K] (g : Kˣ) (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) :
    adjoin F ({(g : K) ^ 2} : Set K) = ⊤ := by sorry
