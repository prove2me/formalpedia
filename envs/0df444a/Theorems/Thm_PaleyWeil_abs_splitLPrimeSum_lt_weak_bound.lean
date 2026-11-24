-- Prove2me | Theorems.Thm_PaleyWeil_abs_splitLPrimeSum_lt_weak_bound
-- name    : PaleyWeil.abs_splitLPrimeSum_lt_weak_bound
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:34:28.570138+00:00
-- url     : https://prove2.me/theorems/ef7508d1-56d4-4b59-944a-80c1187dc9e4
-- title:
--   Uniform weak bounds for every prime-polynomial power sum
-- statement:
--   Let K be a finite field of odd characteristic with q elements, and let s contain m ≥ 3 distinct elements with q > 6m. For every positive integer n, |splitLPrimeSum(s,n)| < 5m(√q)ⁿ.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/PrimePowerBounds.lean lines 16–42; SHA256 5d428cae0e18e75b6f135766b5c68315e47e4f25bbbe1dccc4cbf6673fafb879; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLSeriesDefs
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial Finset
open PaleyWeil

theorem PaleyWeil.abs_splitLPrimeSum_lt_weak_bound {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (hK : ringChar K ≠ 2) (s : Finset K) (hs3 : 3 ≤ s.card)
    (hq : 6 * s.card < Fintype.card K) (n : ℕ) (hn : 0 < n) :
    |(splitLPrimeSum s n : ℝ)| <
      (5 * (s.card : ℝ)) * (Real.sqrt (Fintype.card K)) ^ n := by sorry
