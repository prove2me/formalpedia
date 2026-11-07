-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_prime_residue_coordinate_polynomial_irreducible
-- name    : QEC.Coding.AlgebraicGeometry.prime_residue_coordinate_polynomial_irreducible
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:47:08.279093+00:00
-- url     : https://prove2.me/theorems/7aabeb57-a986-4c75-b91b-7ab5c80f6879
-- title:
--   Algebraic Geometry: prime residue coordinate polynomial irreducible
-- statement:
--   The Algebraic Geometry construction uses the prime residue coordinate polynomial irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L75-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L75-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.prime_residue_coordinate_polynomial_irreducible
    (p : ℕ) [Fact p.Prime] :
    Irreducible ((Polynomial.X : Polynomial (RatFunc (ZMod p)))^p -
      Polynomial.C RatFunc.X) := by sorry
