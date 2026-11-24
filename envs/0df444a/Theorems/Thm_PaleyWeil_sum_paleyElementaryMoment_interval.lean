-- Prove2me | Theorems.Thm_PaleyWeil_sum_paleyElementaryMoment_interval
-- name    : PaleyWeil.sum_paleyElementaryMoment_interval
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:19:26.002823+00:00
-- url     : https://prove2.me/theorems/cd8fd1d8-8705-4a22-b99c-547300b58a3f
-- title:
--   Total elementary Paley moments lie in certified intervals
-- statement:
--   For any finite H in the field of 2659 elements and 3 ≤ j ≤ 33, the sum over x of the jth elementary Paley sign moment lies between binom(|H|,j)(cⱼ − rⱼ) and binom(|H|,j)(cⱼ + rⱼ). Here cⱼ is −1 for even j and 0 for odd j, and rⱼ is the defined integer character radius, equal in this range to floor((j−2)√2659) for even j and floor((j−1)√2659) for odd j.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/Paley2659MomentTotals.lean lines 139–156; SHA256 48456d750e106cb7d7428d46c5d32396fa06995c2bf45fc627d69eac0a4f335f; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659Histogram
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659LowMoments
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659MomentTotals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
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
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.ZMod.Basic
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
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil


open Finset
open PaleyWeil

theorem PaleyWeil.sum_paleyElementaryMoment_interval (H : Finset PaleyField) (j : ℕ)
    (hj3 : 3 ≤ j) (hj33 : j ≤ 33) :
    (Nat.choose H.card j : ℤ) * (paleyCharacterCenter j - paleyCharacterRadius j) ≤
        (∑ x : PaleyField, paleyElementaryMoment H j x) ∧
      (∑ x : PaleyField, paleyElementaryMoment H j x) ≤
        (Nat.choose H.card j : ℤ) * (paleyCharacterCenter j + paleyCharacterRadius j) := by sorry
