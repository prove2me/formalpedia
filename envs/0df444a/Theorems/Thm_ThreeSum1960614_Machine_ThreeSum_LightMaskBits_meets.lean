-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskBits_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightMaskBits.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:25:21.403456+00:00
-- url     : https://prove2.me/theorems/950beeab-6db3-4760-9501-371edb4a8ae8
-- title:
--   Construction of a Boolean row from a subset mask
-- statement:
--   Let $\lambda,P,d,\mu$ be Light limits, program, depth and memory; let $L,m,b,w\in\mathbb N$ be width, mask, output and scratch base. Suppose $P$ contains the mask-row, power-table and recursive erasure bodies; addresses fit words; $d+L+1$ is allowed; $w+L+1$ fits memory; $b+L\le w$; $2^{L+1}$ fits a word; and $m<2^L$. The program writes each of the $L$ Boolean mask bits to $b+j$, constructs the correct powers at $w$, meets its prescribed width-time budget, and preserves every cell below $w$ outside that output row.
--
--   This constructs literal coordinate rows for the local support matrix and independent endpoint tests.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightMaskBits.lean#L42-L113

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
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_powTable_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskErase_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightMaskBits
end ThreeSum.LightMaskBits
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBits
end ThreeSum1960614.Machine.ThreeSum.LightMaskBits
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightMaskBits
open _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightMaskBits.meets {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.body pPowers pErase))
    (hpowers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody)
    (herase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space) (hdst : dst+L ≤ work)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word) (hm : m < 2^L) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,m,dst,work] μ (_root_.ThreeSum.LightMaskBits.time L)
      (fun _ μ' => (∀ j < L, μ' (dst+j) = (_root_.ThreeSum.LightMaskBits.bit L m j : ℤ)) ∧
        _root_.ThreeSum.LightSubsetAddress.Powers μ' work L ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst L) := by sorry
