-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightScales_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightScales.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:58:00.76488+00:00
-- url     : https://prove2.me/theorems/a01cdf53-2b5c-43f1-a0cb-019be97bf25e
-- title:
--   Execution of the exact integer microblock scales
-- statement:
--   Let $n,b,d\in\mathbb N$ and $\mu$ be input length, five-cell destination, depth and memory. Let $\lambda,P$ be limits and a program containing the scale body with its logarithm, rounded cube-root, rounded-half and division helpers at their recorded indices. Suppose addresses fit words, $b+5$ fits memory, $35000000000(n+1)$ fits a word and a nested call is allowed. The procedure writes the exact five scale values, returns
--
--   $$\mu(n),$$
--
--   runs within its prescribed scale time and preserves every cell outside the five-cell output.
--
--   This executes the natural-number schedule underlying the certified runtime exponent.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightScales.lean#L91-L169

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
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
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_seg_cons

namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
end ThreeSum1960614.Machine.ThreeSum.LightSmallDivide


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightScales

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightScales.meets {pMain pLog pCube pHalf pDiv : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.body pLog pCube pHalf pDiv))
    (hlog : P[pLog]? = some _root_.ThreeSum1960614.Machine.Light.log2Body)
    (hcube : P[pCube]? = some _root_.ThreeSum1960614.Machine.Light.cbrtCeilBody)
    (hhalf : P[pHalf]? = some _root_.ThreeSum1960614.Machine.Light.halfBody)
    (hdiv : P[pDiv]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((35000000000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [n,dst] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.time n)
      (fun r μ' => r = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values n) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst 5) := by sorry
