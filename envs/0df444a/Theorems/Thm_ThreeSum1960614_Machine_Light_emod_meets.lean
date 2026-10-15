-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_Light_emod_meets
-- name    : ThreeSum1960614.Machine.Light.emod_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:25:12.294774+00:00
-- url     : https://prove2.me/theorems/ec824e12-66b8-4dc9-809c-9c829339151b
-- title:
--   Correctness and cost of signed remainder
-- statement:
--   Let program $P$ contain the concrete remainder body at index $p$. Under its precondition for execution limits, modulus $M$, magnitude bound $V$, and scratch base $f$, and for $|x|\le V$, the procedure returns $$r=x\bmod M$$ within its specified $\operatorname{emodTime}(|x|,M)$ bound and preserves every cell below $f$.
--
--   Provides the checked signed modular arithmetic used by hashing and bucket construction. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L234-L264

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Emod_reduce_ends
import Theorems.Thm_ThreeSum1960614_Machine_Light_Emod_sign_ends
import Theorems.Thm_ThreeSum1960614_Machine_Light_Emod_table_ends

namespace Light
end Light
namespace Light.Emod
end Light.Emod
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod

variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}

theorem ThreeSum1960614.Machine.Light.emod_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.emodBody) (F : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim Mo V fr)
    (hx : |x| ≤ (V : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [x, Mo, fr] μ (_root_.Light.emodTime x.natAbs Mo) fun r μ' =>
      r = x % (Mo : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' fr := by sorry
