-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_exists_even_psl_parameters
-- name    : QEC.Coding.ExpanderCodes.exists_even_psl_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:46:37.407386+00:00
-- url     : https://prove2.me/theorems/bce74ea5-cdc0-4e25-a800-08034984a1d4
-- title:
--   Expander Codes: exists even psl parameters
-- statement:
--   Full-degree even specializations with the three explicit square roots
--   needed to place both quaternion generator sets in PSL₂.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSquareParameters.lean#L126-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSquareParameters.lean#L126-L157

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField

theorem QEC.Coding.ExpanderCodes.exists_even_psl_parameters (p n : ℕ) [hPrime : Fact p.Prime]
    (hDegree : 1 < n) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0) :
    ∃ y r s i : GaloisField p (2 * n),
      y ≠ 0 ∧ 1 + y ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 ∧
      r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon ∧
      s ^ 2 = y / (1 + y) ∧ i ^ 2 = -1 ∧
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = 2 * n := by sorry
