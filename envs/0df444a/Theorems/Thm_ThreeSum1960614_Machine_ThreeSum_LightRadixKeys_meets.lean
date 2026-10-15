-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightRadixKeys_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:18.544813+00:00
-- url     : https://prove2.me/theorems/d3e9eda9-72b3-4edf-9687-51876859a235
-- title:
--   Execution of the complete ordered radix-key product
-- statement:
--   Let a nonempty integer list $X$ be stored at source $s$, with $|x|\le U$ for each $x\in X$, and let $p$ be a natural radix. Suppose $P$ contains the recursive key-product, radix-row and affine bodies, addresses fit words and $s+|X|\le b$. For every block count $J$, memory $\mu$ storing $X$, and depth $d$, assume the exact key-product space and word budgets fit and $d+J+2$ is allowed. The procedure writes the ordered J-fold radix-key list, preceded by its count $|X|^J$, and returns the address of that count cell. It meets its stated time and preserves all cells below $b$.
--
--   This builds the full ordered global-key enumeration, retaining equal values at distinct positions.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightRadixKeys.lean#L97-L199

import Aesop
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightRadixRows_meets
import Theorems.Thm_ThreeSum_RadixKeyLists_values_bounded

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightRadixKeys
end ThreeSum.LightRadixKeys
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightRadixKeys
end ThreeSum1960614.Machine.ThreeSum.LightRadixKeys
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightRadixKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.meets {pMain pRows pAffine src dst p U : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.body pMain pRows))
    (hrows : P[pRows]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows.body pAffine))
    (haffine : P[pAffine]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.body)
    (base : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+base.length ≤ dst) (hm : 0 < base.length)
    (hbound : ∀ x ∈ base, |x| ≤ (U : ℤ)) :
    ∀ J d : ℕ, ∀ μ : ℕ → ℤ,
      _root_.ThreeSum.LightRadixKeys.space dst base.length J ≤ lim.space → (_root_.ThreeSum.LightRadixKeys.word p U J : ℤ) ≤ lim.word →
      d+J+2 ≤ lim.depth → _root_.ThreeSum1960614.Machine.Light.Seg μ src base →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,base.length,J,p,dst] μ (_root_.ThreeSum.LightRadixKeys.time base.length J)
        (fun r ν => r = ((dst+_root_.ThreeSum.LightRadixKeys.offset base.length J : ℕ) : ℤ) ∧
          ν (dst+_root_.ThreeSum.LightRadixKeys.offset base.length J) = ((base.length^J : ℕ) : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Seg ν (dst+_root_.ThreeSum.LightRadixKeys.offset base.length J+1) (_root_.ThreeSum.RadixKeyLists.values (p : ℤ) base J) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by sorry
