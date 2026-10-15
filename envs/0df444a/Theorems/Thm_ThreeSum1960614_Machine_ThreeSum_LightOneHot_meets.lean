-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOneHot_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightOneHot.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:08:18.116567+00:00
-- url     : https://prove2.me/theorems/fbf0bab3-79ad-4882-a5ab-b7ceae782460
-- title:
--   Recursive mask evaluation reads the exact coefficient choice
-- statement:
--   Suppose two coefficient arrays $w_0,w_1$ of width $W$ and a power table are stored at the specified bases, all coefficients are at most $U$, and their address and word bounds hold. For $L\le W$, $m<2^L$, and allowed depth $d+L$, the recursive hash body returns $\operatorname{eval}(w_0,w_1,L,m)$ within the stated time and leaves memory unchanged.
--
--   This mask-evaluation contract supplies the actual endpoint hashes read by local and block source construction.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOneHot.lean#L38-L125

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
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
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
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
import Theorems.Thm_ThreeSum_OneHotMask_eval_le

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightOneHot
end ThreeSum.LightOneHot
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightOneHot
end ThreeSum1960614.Machine.ThreeSum.LightOneHot
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightOneHot
open _root_.ThreeSum1960614.Machine.ThreeSum.LightOneHot

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.OneHotMask
open _root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightOneHot.meets {pHash W powers src0 src1 U : ℕ}
    (hprog : P[pHash]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightOneHot.body pHash))
    (μ : ℕ → ℤ) (w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hsrc0 : src0+W ≤ lim.space) (hsrc1 : src1+W ≤ lim.space)
    (hword : (_root_.ThreeSum.LightOneHot.word W U : ℤ) ≤ lim.word)
    (hpowers : _root_.ThreeSum.LightSubsetAddress.Powers μ powers W)
    (hread0 : ∀ i < W, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < W, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < W, w0 i ≤ U) (hbound1 : ∀ i < W, w1 i ≤ U) :
    ∀ L m : ℕ, L ≤ W → m < 2^L →
      ∀ d, d+L ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pHash d [L,m,W,powers,src0,src1] μ (_root_.ThreeSum.LightOneHot.time L)
        (fun r μ' => r = (_root_.ThreeSum.OneHotMask.eval w0 w1 L m : ℤ) ∧ μ' = μ) := by sorry
