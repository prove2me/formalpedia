-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightPascal_build_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightPascal.build_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:29:23.998176+00:00
-- url     : https://prove2.me/theorems/ee85aa12-cc97-44cf-9eea-5a393272be5d
-- title:
--   Execution of complete Pascal-table construction
-- statement:
--   Let $L,b\in\mathbb N$, $\mu$ an initial memory and $\lambda,P,d$ limits, program and depth. Suppose the program contains the Pascal builder, fill, row and linear-array bodies at the stated indices. Assume addresses fit words, the complete Pascal-table reservation at $b$ fits memory, $2^{L+1}$ fits a word and $d+1$ is strictly below the depth limit. The call constructs the exact Pascal coefficient table through width $L$, satisfies its prescribed build-time budget and changes no cell outside that table reservation.
--
--   This makes every binomial lookup in compact subset addressing follow from constructed memory.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightPascal.lean#L92-L165

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
import Mathlib.Data.Nat.Choose.Bounds
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightArray_linear_bounded_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightPascal.build_meets {pBuild pFill pRow pLinear : ℕ}
    (hbuild : P[pBuild]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.buildBody pFill pRow))
    (hfill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody)
    (hrow : P[pRow]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.rowBody pLinear))
    (hlinear : P[pLinear]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody)
    {μ : ℕ → ℤ} {dst L : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hspace : dst+_root_.ThreeSum.LightPascal.tableSize L ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pBuild d [dst,L] μ (_root_.ThreeSum.LightPascal.buildTime L) fun _ μ' =>
      _root_.ThreeSum.LightPascal.Table μ' dst L ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (_root_.ThreeSum.LightPascal.tableSize L) := by sorry
