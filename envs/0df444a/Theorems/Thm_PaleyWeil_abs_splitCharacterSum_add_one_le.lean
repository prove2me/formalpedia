-- Prove2me | Theorems.Thm_PaleyWeil_abs_splitCharacterSum_add_one_le
-- name    : PaleyWeil.abs_splitCharacterSum_add_one_le
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:34:24.80778+00:00
-- url     : https://prove2.me/theorems/ea061a78-4c0f-45ed-ad1b-1b59220e990c
-- title:
--   Centered square-root bound for even-degree split character sums
-- statement:
--   Let K be a finite field of odd characteristic with q elements and let s have even cardinality m ≥ 4, with q > 6m. Then |splitCharacterSum(s) + 1| ≤ (m−2)√q.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitSharpBound.lean lines 45–69; SHA256 e7be84a81828ba9d4c718bbd2a28b6063de7d442ece1c1b175a2510805bdceb6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitEvenReduction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Weight
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
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


/-!
Sharp Weil bounds for products of distinct linear factors. The proof combines
the exact unique-factorization recurrence with the verified weak Stepanov
estimate in every finite extension and complex power-sum amplification.
-/
open Polynomial Finset
open scoped PowerSeries
open PaleyWeil
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem PaleyWeil.abs_splitCharacterSum_add_one_le (hK : ringChar K ≠ 2) (s : Finset K)
    (hs4 : 4 ≤ s.card) (hq : 6 * s.card < Fintype.card K) (heven : Even s.card) :
    |(splitCharacterSum s : ℝ) + 1| ≤
      ((s.card - 2 : ℕ) : ℝ) * Real.sqrt (Fintype.card K) := by sorry
