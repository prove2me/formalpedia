-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightZetaPass_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightZetaPass.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:13:12.203979+00:00
-- url     : https://prove2.me/theorems/bc0b0eb6-7962-45ee-80fa-300527c54adb
-- title:
--   A complete compact zeta pass
-- statement:
--   Let a width-$L$ subset function $f$ be stored on the compact downset through cutoff $c\le L$, with values bounded by $U$. Fix a coordinate $a$. Suppose source and destination tables are disjoint before mask scratch, all masks precede work scratch, Pascal and powers fit space, the stated address/word bounds including $2U$ hold, the concrete enumeration and cell interfaces are present, and depth $d+L+6$ is available. The routine stores the entire exact zeta step in its stated time and preserves other cells below mask scratch.
--
--   Implements a full transform pass over compact enumerated layers. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightZetaPass.lean#L54-L152

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Data.Finset.Card
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
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightZetaBatch_meets
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LightZetaPass
end ThreeSum.LightZetaPass
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaPass
end ThreeSum1960614.Machine.ThreeSum.LightZetaPass
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightZetaPass
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaPass

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightZetaPass.meets
    {pMain pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaPass.body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell.body pSetup pOffset pErase pRank))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body)
    (hErase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst maskBase work U d : ℕ}
    (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ L)
    (hsrc : src+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ maskBase) (hdst : dst+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hsep : _root_.Light.Apart src (_root_.ThreeSum.SubsetAddress.downsetCap L cut) dst (_root_.ThreeSum.SubsetAddress.downsetCap L cut))
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : _root_.ThreeSum.LightZetaCell.TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+6 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cut,a.val,src,dst,maskBase,work] μ (_root_.ThreeSum.LightZetaPass.time L cut)
      (fun _ μ' => _root_.ThreeSum.LightZetaCell.TableAt μ' dst cut (_root_.ThreeSum.Subset.zetaStep a f) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase dst (_root_.ThreeSum.SubsetAddress.downsetCap L cut)) := by sorry
