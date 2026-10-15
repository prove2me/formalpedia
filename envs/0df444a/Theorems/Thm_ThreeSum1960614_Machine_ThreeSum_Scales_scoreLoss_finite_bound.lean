-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Scales_scoreLoss_finite_bound
-- name    : ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss_finite_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:38:16.570134+00:00
-- url     : https://prove2.me/theorems/2976ce57-4b9d-4151-bd40-6fb82e09c082
-- title:
--   Finite contraction bound for the accumulated prime score
-- statement:
--   Let $k,n,H,H_1,P\in\mathbb N$. Write $C$ for the number of candidate primes, $Y$ for the prime window, $D$ for the divisor budget, $d$ for the prescribed prime depth, and $b$ for the input bit width at size $n$. Suppose $C>0$, $DY\le C\,4(k+2)(b+1)$, $C^dH\le D^dH_1$, and $P\le(4Y)^d$. Then $$PH\le L_k(n)H_1,$$ where $L_k(n)$ is the specified score-loss factor.
--
--   Converts repeated score contraction into the explicit finite loss appearing in the runtime analysis. This is a supporting lemma in the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/Scales.lean#L691-L724

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Filter
end Filter
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

open _root_.Filter
open _root_.Real
open scoped _root_.Topology
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

theorem ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss_finite_bound {k n H H₁ P : ℕ}
    (hC : 0 < (_root_.ThreeSum.PrimeDensity.candidates (_root_.ThreeSum.Scales.primeWindow n)).card)
    (hbudget : _root_.ThreeSum.Scales.divisorBudget k n * _root_.ThreeSum.Scales.primeWindow n ≤
      (_root_.ThreeSum.PrimeDensity.candidates (_root_.ThreeSum.Scales.primeWindow n)).card * (4 * (k + 2) * (_root_.ThreeSum.Scales.inputBits n + 1)))
    (hcontract : (_root_.ThreeSum.PrimeDensity.candidates (_root_.ThreeSum.Scales.primeWindow n)).card ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * H ≤
      _root_.ThreeSum.Scales.divisorBudget k n ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * H₁)
    (hP : P ≤ (4 * _root_.ThreeSum.Scales.primeWindow n) ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :
    P * H ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n * H₁ := by sorry
