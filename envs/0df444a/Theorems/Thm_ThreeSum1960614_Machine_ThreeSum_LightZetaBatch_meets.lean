-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightZetaBatch_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightZetaBatch.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:09:06.18284+00:00
-- url     : https://prove2.me/theorems/09c5ced3-5bc6-4c94-bebf-6c5a12dde160
-- title:
--   Updating one stored mask layer in a zeta pass
-- statement:
--   Let $f$ be a subset table of width $L$ and cutoff $c$, with values bounded by $U$, and let a stored mask list consist of valid masks of common cardinality at most $c$. For coordinate $a$, assume separate source and destination compact tables, mask storage disjoint from the destination, and the full helper, scratch, word, and depth bounds. The batch program writes the specified coordinate-update values at the listed masks while retaining other destination entries; it preserves memory outside destination and scratch and meets its stated time.
--
--   This batch contract is the finite coordinate-update step used to build every stored compact zeta stage.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightZetaBatch.lean#L41-L126

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightZetaCell_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_injective
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightZetaBatch
end ThreeSum.LightZetaBatch
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaBatch
end ThreeSum1960614.Machine.ThreeSum.LightZetaBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightZetaBatch
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaBatch

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightZetaBatch.meets {pMain pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaBatch.body pCell))
    (hcell : P[pCell]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell.body pSetup pOffset pErase pRank))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body)
    (hErase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut cardinal maskBase src dst work U d : ℕ}
    (masks : List ℕ) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work) (hdst : dst+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hmasks : maskBase+masks.length ≤ work)
    (hsepSrc : _root_.Light.Apart src (_root_.ThreeSum.SubsetAddress.downsetCap L cut) dst (_root_.ThreeSum.SubsetAddress.downsetCap L cut))
    (hsepMasks : _root_.Light.Apart maskBase masks.length dst (_root_.ThreeSum.SubsetAddress.downsetCap L cut))
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : _root_.ThreeSum.LightZetaCell.TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hseg : _root_.ThreeSum1960614.Machine.Light.SegN μ maskBase masks)
    (hvalid : ∀ m ∈ masks, _root_.ThreeSum.SubsetAddress.IsMask L cardinal m) (hcardinal : cardinal ≤ cut)
    (hd : d+L+5 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cardinal,masks.length,maskBase,a.val,src,dst,work]
      μ (_root_.ThreeSum.LightZetaBatch.time L masks.length)
      (fun _ μ' => _root_.ThreeSum.LightZetaCell.TableAt μ' dst cut (_root_.ThreeSum.LightZetaBatch.values μ dst masks a f) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst (_root_.ThreeSum.SubsetAddress.downsetCap L cut)) := by sorry
