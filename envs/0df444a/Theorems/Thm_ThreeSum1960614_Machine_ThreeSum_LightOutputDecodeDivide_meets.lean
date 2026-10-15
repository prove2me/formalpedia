-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeDivide_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:29:26.024443+00:00
-- url     : https://prove2.me/theorems/6711067b-68b9-4bb5-9bed-8f6aaedb4792
-- title:
--   Division through the retained doubling-table routine
-- statement:
--   Let $a,M,V,f\in\mathbb N$, with $a\le V$, and let $\lambda,P,d,\mu$ be limits, program, depth and memory. Suppose $M,V,f$ satisfy the verified remainder precondition, including positive modulus, sufficient word magnitude and logarithmic scratch space. If the selected procedure is the output-decoding division body, it returns
--
--   $$\lfloor a/M\rfloor$$
--
--   within the specified division time and preserves every memory cell below $f$.
--
--   This performs physical output-index decoding using only the allowed arithmetic and scratch operations.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOutputDecodeDivide.lean#L98-L116

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Emod_table_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeDivide_reduce_ends

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

theorem ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.meets {pMain : ℕ} (hmain : P[pMain]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body)
    (F : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim Mo V fr) (haV : a ≤ V) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,Mo,fr] μ (_root_.ThreeSum.LightOutputDecodeDivide.time a Mo)
      (fun q ν => q = ((a/Mo : ℕ) : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν fr) := by sorry
