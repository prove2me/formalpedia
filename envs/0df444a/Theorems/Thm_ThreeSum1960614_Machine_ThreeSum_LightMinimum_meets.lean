-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMinimum_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightMinimum.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:41:56.809318+00:00
-- url     : https://prove2.me/theorems/fb5e6ac8-b334-40c6-bda4-5fa893afe658
-- title:
--   Execution of least-index minimum selection
-- statement:
--   Let $\lambda,P,d,\mu$ be limits, program, depth and memory. Let $a,n\in\mathbb N$ with $n>0$, and $f:\mathbb N\to\mathbb Z$. Suppose procedure $p$ is the minimum body, addresses fit words, the $n$ source cells at $a$ fit memory and store $f(0),\ldots,f(n-1)$. The call returns the least index minimizing $f$ on that range:
--
--   $$r=\min\operatorname*{arg\,min}_{i<n}f(i),$$
--
--   within its prescribed $n$-dependent time, leaving memory unchanged.
--
--   This fixes deterministic first-minimum choices in offset and greedy-selection implementations.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightMinimum.lean#L65-L99

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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightMinimum
end ThreeSum1960614.Machine.ThreeSum.LightMinimum

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightMinimum
open _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightMinimum.meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.body)
    {μ : ℕ → ℤ} {src n : ℕ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n)
    (hsrc : src+n ≤ lim.space)
    (hread : ∀ i < n, μ (src+i) = f i) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [src, n] μ (_root_.ThreeSum.LightMinimum.time n)
      fun r μ' => r = (_root_.ThreeSum.LightMinimum.least f n : ℤ) ∧ μ' = μ := by sorry
