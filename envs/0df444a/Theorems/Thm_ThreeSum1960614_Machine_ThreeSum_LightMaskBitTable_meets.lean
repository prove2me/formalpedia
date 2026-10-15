-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskBitTable_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:48.706484+00:00
-- url     : https://prove2.me/theorems/3fa6bbbe-9b29-4d9c-a743-a085bcab0ed3
-- title:
--   Execution of the complete mask-bit table
-- statement:
--   Let $L,n\in\mathbb N$, mask list $m_i<2^L$, source base $a$, table base $b$, scratch $w$, and $\lambda,P,d,\mu$ limits, program, depth and memory be given. Suppose the wrapper, bit-row, powers and recursive erasure bodies occur in $P$; the source list is correct in $\mu$; addresses fit words; $a+n\le b$; $b+nL\le w$; $w+L+1$ fits memory; $2^{L+1}$ fits a word; and $d+L+2$ is allowed. Then it writes
--
--   $$\nu(b+iL+j)=\operatorname{bit}_j(m_i)\quad(i<n,\ j<L),$$
--
--   meets its stated time and preserves cells below $w$ outside the table.
--
--   This constructs literal Boolean support rows used by all-pairs retained-edge testing.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightMaskBitTable.lean#L24-L78

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskBits_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightMaskBitTable
end ThreeSum.LightMaskBitTable
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable
end ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightMaskBitTable
open _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1000000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable.meets {pMain pBits pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBitTable.body pBits))
    (hbits : P[pBits]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.body pPowers pErase))
    (hpowers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody)
    (herase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L masks dst n work : ℕ} (mask : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hdst : dst+n*L ≤ work)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,masks,dst,n,work] μ (_root_.ThreeSum.LightMaskBitTable.time L n)
      (fun _ μ' =>
        (∀ i < n, ∀ a < L, μ' (dst+i*L+a) = (_root_.ThreeSum.LightMaskBits.bit L (mask i) a : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst (n*L)) := by sorry
