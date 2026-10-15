-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightDownsetEnumeration_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:25:18.69022+00:00
-- url     : https://prove2.me/theorems/dfb72ca9-6cdc-47db-bfe0-7b7774ef321b
-- title:
--   Execution of compact downset enumeration
-- statement:
--   Let $L,c,a,p,d\in\mathbb N$ be width, cutoff, destination, powers base and depth, with $c\le L$. Suppose the Light program contains the downset wrapper and recursive layer enumerator; memory $\mu$ has the correct $L+1$ powers table; addresses fit words; the powers fit memory and $2^{L+1}$ fits a word. Assume the complete output of capacity $D(L,c)$ ends before the power table and $d+L+1$ is permitted. Then the call returns
--
--   $$D(L,c)=\sum_{i=0}^{c}\binom Li,$$
--
--   writes the exact ordered compact downset enumeration at $a$, runs within its prescribed budget and preserves every cell outside that capacity.
--
--   This constructs the compact mask domain used by stored subset transforms.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightDownsetEnumeration.lean#L69-L143

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetEnumeration_meets
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightDownsetEnumeration
end ThreeSum.LightDownsetEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightDownsetEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.meets {pMain pEnum L cut dst powers d : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumeration.body pEnum))
    (henum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ powers)
    (hpowers : _root_.ThreeSum.LightSubsetAddress.Powers μ powers L) (hd : d+L+1 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cut,dst,powers] μ (_root_.ThreeSum.LightDownsetEnumeration.time L cut)
      (fun r μ' => r = (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (_root_.ThreeSum.SubsetAddress.enumerateDownset L cut) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (_root_.ThreeSum.SubsetAddress.downsetCap L cut)) := by sorry
