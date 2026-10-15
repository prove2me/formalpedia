-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSupportMark_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSupportMark.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:06.639066+00:00
-- url     : https://prove2.me/theorems/96671002-d33e-4d62-b0d4-95d913c90ea8
-- title:
--   Correct support marking with repeated keys
-- statement:
--   Let stored arrays contain $n$ keys below $p$ and their natural validity flags. Suppose the fill and marking bodies are present, the key and flag segments are disjoint from the $p$-cell destination, all segments fit space, addresses fit words, $1$ fits the word bound, and call depth is available. The routine writes the exact support bit for each key, counting an index only when its flag equals one, in the specified time and changes no other cells.
--
--   Converts repeated valid representations into a Boolean support table. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSupportMark.lean#L123-L152

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
import Definitions.Def_ThreeSum1962Source_Bundle03
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
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
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

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSupportMark
end ThreeSum.LightSupportMark
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSupportMark
end ThreeSum1960614.Machine.ThreeSum.LightSupportMark

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSupportMark
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSupportMark.meets {pMain pFill : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.body pFill)) (hfill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody)
    {μ : ℕ → ℤ} {keys flags dst n p : ℕ}
    (key valid : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hK : keys+n ≤ lim.space) (hF : flags+n ≤ lim.space) (hD : dst+p ≤ lim.space)
    (hsepK : _root_.Light.Apart keys n dst p) (hsepF : _root_.Light.Apart flags n dst p)
    (hkeys : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hflags : ∀ i < n, μ (flags+i) = (valid i : ℤ))
    (hkeyLt : ∀ i < n, key i < p) (hword : (1 : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [keys,flags,dst,n,p] μ (_root_.ThreeSum.LightSupportMark.time n p)
      (fun _ μ' => (∀ r < p, μ' (dst+r) = (_root_.ThreeSum.LightSupportMark.bit key valid r n : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst p) := by sorry
