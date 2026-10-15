-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightRow_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightWeightRow.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:52:49.512327+00:00
-- url     : https://prove2.me/theorems/868dc776-3ca1-424b-9437-d30ff222227d
-- title:
--   Decoding an arithmetic progression of weight coordinates
-- statement:
--   Let a stored table contain $p^e$ for $e\le W$, with $p\ge1$. Suppose all requested coordinates $a+si$ for $i<n$ are below $W$, the power table and output are disjoint and fit space, and the stated word, address, and two-level depth bounds hold. With the concrete digit and quotient procedures, the row routine writes the prescribed base-$p$ digit of candidate $k$ at each requested coordinate within its stated time, changing only the output.
--
--   Decodes candidate coefficient rows by actual bounded arithmetic. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightWeightRow.lean#L36-L114

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightRadixDigit_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightWeightRow
end ThreeSum.LightWeightRow
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightRow
end ThreeSum1960614.Machine.ThreeSum.LightWeightRow

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightWeightRow
open _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightRow

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1200000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightWeightRow.meets {pMain pDigit pDivide : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWeightRow.body pDigit))
    (hdigit : P[pDigit]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    {μ : ℕ → ℤ} {W p k powers start stride dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hp : 1 ≤ p)
    (hspace : dst+n ≤ lim.space) (hpowers : powers+(W+1) ≤ lim.space)
    (hsep : _root_.Light.Apart powers (W+1) dst n)
    (hword : (_root_.ThreeSum.LightWeightRow.word W p k start stride : ℤ) ≤ lim.word)
    (hcoords : ∀ i < n, start+stride*i < W)
    (hread : ∀ e ≤ W, μ (powers+e) = ((p^e : ℕ) : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [W,p,k,powers,start,stride,dst,n] μ (_root_.ThreeSum.LightWeightRow.time n k)
      (fun _ μ' =>
        (∀ i < n, μ' (dst+i) = (_root_.ThreeSum.WeightEnumeration.digit p W k (start+stride*i) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n) := by sorry
