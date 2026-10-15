-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceRowFlag_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:28:38.738833+00:00
-- url     : https://prove2.me/theorems/cbeb8060-69ba-4e1b-8664-cf94c486a623
-- title:
--   Both independent trimming flags for a physical row
-- statement:
--   Let a stored Boolean row have width $L$, desired cardinality $h\le L$, coefficient rows bounded by $U$, and two stored histograms bounded by $V$ modulo $p>0$. Suppose the scan, remainder, flag-test, and wrapper bodies are present; all source arrays, histograms, and two output cells precede scratch; and the stated space, word, address, and depth bounds hold. The procedure writes the exact left-orientation and right-orientation flags using their independent histograms, in its prescribed time, preserving other cells below scratch.
--
--   Implements independent source trimming for one actual mask row. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceRowFlag.lean#L50-L162

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_emod_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceFlagTest_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceRowScan_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSourceRowFlag
end ThreeSum.LightSourceRowFlag
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag
end ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceRowFlag
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.meets {pMain pRow pEmod pFlag : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowFlag.body pRow pEmod pFlag))
    (hrow : P[pRow]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRowScan.body)
    (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    (hflag : P[pFlag]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceFlagTest.body)
    {μ : ℕ → ℤ} {src src0 src1 L h histL histR p cap dst work U V : ℕ}
    (bits w0 w1 leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hp : 0 < p) (hh : h ≤ L)
    (hsrc : src+L ≤ work) (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hleft : histL+p ≤ work) (hright : histR+p ≤ work) (hdst : dst+2 ≤ work)
    (hspace : _root_.ThreeSum.LightSourceRowFlag.space work L U ≤ lim.space) (hword : (_root_.ThreeSum.LightSourceRowFlag.word L p U V cap : ℤ) ≤ lim.word)
    (hbits : ∀ i < L, μ (src+i) = (bits i : ℤ))
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbitBound : ∀ i < L, bits i ≤ 1)
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U)
    (hcountL : ∀ r < p, μ (histL+r) = (leftCount r : ℤ))
    (hcountR : ∀ r < p, μ (histR+r) = (rightCount r : ℤ))
    (hcountBoundL : ∀ r < p, leftCount r ≤ V)
    (hcountBoundR : ∀ r < p, rightCount r ≤ V) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,src0,src1,L,h,histL,histR,p,cap,dst,work] μ (_root_.ThreeSum.LightSourceRowFlag.time L U)
      (fun _ ν => ν dst = (_root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w0 w1 leftCount : ℤ) ∧
        ν (dst+1) = (_root_.ThreeSum.LightSourceRowFlag.flag L h p cap bits w1 w0 rightCount : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν work dst 2) := by sorry
