-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_coprime_thetaLevel
-- name    : QEC.Coding.TannerLiftedProduct.LPSResiduePrime.coprime_thetaLevel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:30:36.838926+00:00
-- url     : https://prove2.me/theorems/f641f03e-7116-42ac-9993-5ee3ca3dbb66
-- title:
--   LPSResidue Prime: coprime theta Level
-- statement:
--   The LPS degree prime is a good prime for the level `16q²` used by the
--   four-variable trace theta form [LPS, §4].  This is only a coprimality fact;
--   it does not assert modularity or a Hecke coefficient bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L129-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResiduePrime.lean#L129-L140

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix

theorem QEC.Coding.TannerLiftedProduct.LPSResiduePrime.coprime_thetaLevel
    (a : LPSResiduePrime p) : Nat.Coprime p (16 * a.q ^ 2) := by sorry
