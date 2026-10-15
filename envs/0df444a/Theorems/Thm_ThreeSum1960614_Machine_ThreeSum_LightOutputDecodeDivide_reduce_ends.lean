-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeDivide_reduce_ends
-- name    : ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.reduce_ends
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:13:29.227268+00:00
-- url     : https://prove2.me/theorems/b2e5ae2b-7f41-46ed-ae98-df7bd281a090
-- title:
--   Quotient-and-remainder reduction from a doubling table
-- statement:
--   Let $\lambda,P,d$ be Light limits, program and depth; let $a,M,V,f\in\mathbb N$ and memories $\mu,\nu$ satisfy the remainder precondition for positive modulus $M$, magnitude bound $V$ and scratch base $f$, with $a\le V$. Suppose the doubling table for $a,M$ is stored from $\mu$ to $\nu$, and let $t\in\mathbb Z$ be an arbitrary retained local value. Writing $R$ for the number of doubling rounds, the reduction statement transforms the local frame $(a,M,f,a,R,t,0)$ into
--
--   $$(a,M,f,a\bmod M,0,t,\lfloor a/M\rfloor)$$
--
--   within $60R+4$ steps, leaving memory exactly $\nu$.
--
--   This supplies a division-free physical quotient/remainder operation for global-output decoding.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOutputDecodeDivide.lean#L43-L96

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while

namespace Light
end Light
namespace Light.Emod
end Light.Emod
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightOutputDecodeDivide
end ThreeSum.LightOutputDecodeDivide
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightOutputDecodeDivide
open _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.reduce_ends (F : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim Mo V fr) (haV : a ≤ V) {t : ℤ}
    (tab : _root_.ThreeSum1960614.Machine.Light.Emod.Table μ ν Mo fr (_root_.Light.emodRounds a Mo)) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.reduce ⟨_root_.Light.frame [a,Mo,fr,a,_root_.Light.emodRounds a Mo,t,0],ν⟩
      (60*_root_.Light.emodRounds a Mo+4)
      (fun σ => σ = ⟨_root_.Light.frame [a,Mo,fr,(a%Mo : ℕ),0,t,(a/Mo : ℕ)],ν⟩) := by sorry
