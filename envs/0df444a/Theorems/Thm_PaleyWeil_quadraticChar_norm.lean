-- Prove2me | Theorems.Thm_PaleyWeil_quadraticChar_norm
-- name    : PaleyWeil.quadraticChar_norm
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:15.518586+00:00
-- url     : https://prove2.me/theorems/96e75bd1-4ca5-4b57-811b-fcc8cc5c8cf7
-- title:
--   Quadratic characters commute with finite-field norms
-- statement:
--   For a finite extension L/K of finite fields of odd characteristic and every x ∈ L, χₖ(Normₗ/ₖ(x)) = χₗ(x).
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/QuadraticNorm.lean lines 19–50; SHA256 30da2291071def018d94bb12baeb0d5f9860a0d6b86a482d9596be0a57334808; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PaleyWeil
end PaleyWeil


open PaleyWeil

theorem PaleyWeil.quadraticChar_norm {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L]
    (hK : ringChar K ≠ 2) (hL : ringChar L ≠ 2) (x : L) :
    quadraticChar K (Algebra.norm K x) = quadraticChar L x := by sorry
