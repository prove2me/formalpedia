-- Prove2me | Theorems.Thm_PaleyWeil_paleyTriple_prefix_relations
-- name    : PaleyWeil.paleyTriple_prefix_relations
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:19:48.325447+00:00
-- url     : https://prove2.me/theorems/11aeda90-eb36-4074-b35d-e847b836e365
-- title:
--   Exact relations among the three Paley triple prefix counts
-- statement:
--   For a three-element set H, put T = paleyPrefixCount(H,0) and I = paleyInternalPairCount(H). Then paleyPrefixCount(H,1) = 1992 − I − 2T and paleyPrefixCount(H,2) = 1992 + I + T, with the identities interpreted over the integers.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/Paley2659TripleHull.lean lines 146–198; SHA256 d33dbde2a2e2f217f7706e4986fe9757fd3395ced1e63759a3f6f9c3a8a5b600; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659LowMoments
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659PopulationMajorant
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659TripleHull
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
import Mathlib.Data.Fin.VecNotation
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
namespace Polynomial
end Polynomial


/-! Analytic, score-conditioned population hulls for three Paley vertices.

No enumeration of field elements or triples is used. The two possible internal
score types give a one-dimensional affine family, whose endpoints follow from
the proved cubic character estimate. Four-vertex orbit hulls are unnecessary for
the retained campaign certificate.
-/
open Finset Polynomial
open PaleyWeil
open scoped Classical

theorem PaleyWeil.paleyTriple_prefix_relations (H : Finset PaleyField) (hH : H.card = 3) :
    (paleyPrefixCount H 1 : ℤ) =
        1992 - (paleyInternalPairCount H : ℤ) - 2 * (paleyPrefixCount H 0 : ℤ) ∧
      (paleyPrefixCount H 2 : ℤ) =
        1992 + (paleyInternalPairCount H : ℤ) + (paleyPrefixCount H 0 : ℤ) := by sorry
