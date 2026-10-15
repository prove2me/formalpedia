-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightPrimality_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightPrimality.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:03.864742+00:00
-- url     : https://prove2.me/theorems/da442513-50fa-4fbe-9ae5-68748c8039ac
-- title:
--   Execution of deterministic primality testing
-- statement:
--   Let $2\le n\le V$, scratch base $w$, memory $\mu$, and $\lambda,P,d$ limits, program and depth be given. Suppose the primality and remainder bodies occur in $P$; addresses fit words; a nested call is allowed; $w+\lfloor\log_2(V+1)\rfloor+2$ fits memory; and $8V+16$ fits a word. The procedure returns the exact primality indicator of $n$ within its specified $(n,V)$ time and preserves every cell below $w$.
--
--   This makes local and auxiliary prime construction executable without a primality oracle.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightPrimality.lean#L97-L156

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
import Definitions.Def_ThreeSum1962Source_Bundle03
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
import Mathlib.Data.Nat.Prime.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_Light_emod_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPrimality
end ThreeSum.LightPrimality
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimality
end ThreeSum1960614.Machine.ThreeSum.LightPrimality
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightPrimality
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimality

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightPrimality.meets {pMain pEmod : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimality.body pEmod))
    (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    {μ : ℕ → ℤ} {n free maxValue : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hn : 2 ≤ n) (hmax : n ≤ maxValue)
    (hspace : free+(Nat.log 2 (maxValue+1)+2) ≤ lim.space)
    (hword : (8*maxValue+16 : ℕ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [n,free] μ (_root_.ThreeSum.LightPrimality.time n maxValue)
      (fun r μ' => r = (_root_.ThreeSum.LightPrimality.answer n : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' free) := by sorry
