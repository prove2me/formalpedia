-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBooleanDot_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBooleanDot.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:28:20.002378+00:00
-- url     : https://prove2.me/theorems/c8158fdc-31a3-4832-ad50-97114859a230
-- title:
--   Computing the Boolean dot product
-- statement:
--   Suppose two stored arrays $f,g$ of length $n$ have values at most one. If their extents fit memory, addresses fit words, and one fits a word, the installed Boolean-dot procedure returns the exact Boolean-dot value within its declared time and preserves memory.
--
--   This Boolean operation computes row coverage against the current active set in the executed greedy-cover algorithm.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBooleanDot.lean#L48-L90

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBooleanDot
end ThreeSum.LightBooleanDot
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBooleanDot
end ThreeSum1960614.Machine.ThreeSum.LightBooleanDot

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBooleanDot
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBooleanDot

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open scoped _root_.BigOperators
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightBooleanDot.meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBooleanDot.body)
    {μ : ℕ → ℤ} {srcA srcB n : ℕ} (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA+n ≤ lim.space) (hB : srcB+n ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA+i) = (f i : ℤ))
    (hreadB : ∀ i < n, μ (srcB+i) = (g i : ℤ))
    (hf : ∀ i < n, f i ≤ 1) (hg : ∀ i < n, g i ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [srcA,srcB,n] μ (_root_.ThreeSum.LightBooleanDot.time n)
      (fun r μ' => r = (_root_.ThreeSum.LightBooleanDot.dot f g n : ℤ) ∧ μ' = μ) := by sorry
