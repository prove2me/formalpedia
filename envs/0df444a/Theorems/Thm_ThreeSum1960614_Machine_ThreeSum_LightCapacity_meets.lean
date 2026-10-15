-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCapacity_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightCapacity.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:39:21.605642+00:00
-- url     : https://prove2.me/theorems/676298ca-9324-437f-926c-4bf5faa35423
-- title:
--   Computing the Karatsuba capacity
-- statement:
--   For positive natural $p$, with $2p+1$ fitting a word and the capacity body installed, the call on $p$ returns the exact Karatsuba interface capacity within its declared time and leaves memory unchanged.
--
--   This capacity contract supplies the concrete padded polynomial length used by the executed convolution routine.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightCapacity.lean#L27-L58

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_of_blockSafe
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightCapacity
end ThreeSum.LightCapacity
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightCapacity
end ThreeSum1960614.Machine.ThreeSum.LightCapacity

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightCapacity
open _root_.ThreeSum1960614.Machine.ThreeSum.LightCapacity

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightCapacity.meets {pMain p : ℕ} (hmain : P[pMain]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightCapacity.body)
    (μ : ℕ → ℤ) (hp : 0 < p)
    (hword : ((2*p+1 : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [p] μ (_root_.ThreeSum.LightCapacity.time p)
      (fun r μ' => r = (_root_.ThreeSum.KaratsubaInterface.capacity p : ℤ) ∧ μ' = μ) := by sorry
