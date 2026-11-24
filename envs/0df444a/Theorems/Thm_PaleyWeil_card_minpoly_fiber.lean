-- Prove2me | Theorems.Thm_PaleyWeil_card_minpoly_fiber
-- name    : PaleyWeil.card_minpoly_fiber
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:35:39.763845+00:00
-- url     : https://prove2.me/theorems/f034f260-7901-459d-a96e-19403c889f0b
-- title:
--   Each minimal polynomial fiber has cardinality equal to its degree
-- statement:
--   In a finite extension L/K of finite fields, for every x ∈ L the number of y ∈ L having the same minimal polynomial over K as x equals the degree of that minimal polynomial.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/WeightedMinpolySum.lean lines 7–37; SHA256 5aa7f916d765c1c82899a8b4955d8d607824d4ea27579457ffa4acea86b616c0; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial Finset
open PaleyWeil

theorem PaleyWeil.card_minpoly_fiber {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L] (x : L) :
    (Finset.univ.filter (fun y : L ↦ minpoly K y = minpoly K x)).card =
      (minpoly K x).natDegree := by sorry
