-- Prove2me | Theorems.Thm_PaleyWeil_paleyUnaryBound_23_4
-- name    : PaleyWeil.paleyUnaryBound_23_4
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:22:30.903371+00:00
-- url     : https://prove2.me/theorems/c5b6f9ba-a085-4384-98eb-886b6ee70529
-- title:
--   Paley population bound with $|H|=23$ and $4$ allowed failures
-- statement:
--   Let $F=\mathbb{F}_{2659}$, let $\chi:F\to\{-1,0,1\}$ be its quadratic character, and let $H\subseteq F$ have cardinality $23$. For $x\in F$, put
--
--   $$p_H(x)=\bigl|\{a\in H:\chi(x-a)=1\}\bigr|.$$
--
--   The number of points outside $H$ with at most $4$ negative character values satisfies
--
--   $$\bigl|\{x\in F\setminus H:p_H(x)\ge 19\}\bigr|\le 237.$$
--
--   This is one of the uniform Paley population bounds used by the unary stage of the sensitivity construction. It holds for every set of the stated size.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/PaleyUnary/Bounds23.lean lines 54–58; SHA256 cb557f7c3e9f21bf76094e5f2b3efabc3460d682b3262f11fbcb480daea991da; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659LowMoments
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659PopulationMajorant
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


/-! Generated exact certificates for Paley2659 unary prefix populations.

Source: analysis/exact-no-quartic-prefix-certificates.json
SHA256: dc3ad7df3e611e464a1f7c632fda6cf4741ab8f9fa4fecbec6468ba3c73aa95f
Only the ordinary moments of degrees 1, 2, 3 and the proved signed Weil
intervals are used. No ordinary quartic codegree bound is assumed.
Every finite comparison below is checked by the Lean kernel with `decide`.
The original campaign checkpoint is preserved unchanged.
-/
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
open Finset
open PaleyWeil

theorem PaleyWeil.paleyUnaryBound_23_4 (H : Finset PaleyField) (hH : H.card = 23) :
    paleyPrefixCount H 4 ≤ 237 := by sorry
