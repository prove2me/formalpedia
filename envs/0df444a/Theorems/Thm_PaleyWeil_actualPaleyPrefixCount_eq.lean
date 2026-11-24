-- Prove2me | Theorems.Thm_PaleyWeil_actualPaleyPrefixCount_eq
-- name    : PaleyWeil.actualPaleyPrefixCount_eq
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:19:45.628849+00:00
-- url     : https://prove2.me/theorems/54869df8-43f7-4141-96ac-829380962ff2
-- title:
--   The concrete Paley graph and finite-field prefix counts agree
-- statement:
--   For every H ⊆ Fin 2659 and every allowed number of failures, the prefix population defined from the concrete paley2659Arc relation equals the field-theoretic Paley prefix population of the image of H under paleyFinEquiv.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/PaleyActualModel.lean lines 86–101; SHA256 f70e456b93c37e510d0140cb271182ef04c68c8d2cb7ddd1eb69c92ae78e96b4; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659PopulationMajorant
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_PaleyActualModel
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
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
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
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Exact identification with the campaign's Fin2659 nonzero-square orientation. -/
open Finset
open SensitivityRankedConstruction
open PaleyWeil
open scoped Classical

theorem PaleyWeil.actualPaleyPrefixCount_eq (H : Finset (Fin 2659)) (failures : ℕ) :
    actualPaleyPrefixCount H failures = paleyPrefixCount (paleyFieldSet H) failures := by sorry
