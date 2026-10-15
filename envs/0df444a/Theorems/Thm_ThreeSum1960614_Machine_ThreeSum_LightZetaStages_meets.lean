-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightZetaStages_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightZetaStages.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:18:52.995458+00:00
-- url     : https://prove2.me/theorems/b055df83-bd92-43d4-ba09-76e37a458629
-- title:
--   Constructing every compact zeta stage
-- statement:
--   Let $f$ be an integer subset table on width $L$, cutoff $c\le L$, with $|f(S)|\le U$ on the downset. Suppose stage zero is stored, the full stage slab precedes mask scratch, and the enumerator, rank, erase, Pascal, word, space, and $d+L+7$ depth requirements hold. The procedure stores all stages through $L$ within its declared time and changes only the stage slab and permitted scratch.
--
--   This transform theorem supplies every retained compact zeta stage needed by later source and sparse-query lookups.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightZetaStages.lean#L48-L169

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightDownsetSize_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightZetaPass_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le
import Theorems.Thm_ThreeSum_Subset_partialZeta_insert

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
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.SubsetStages
end ThreeSum.SubsetStages
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
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaStages
end ThreeSum1960614.Machine.ThreeSum.LightZetaStages
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SubsetStages
end ThreeSum1960614.Machine.ThreeSum.SubsetStages

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightZetaStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetStages
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightZetaStages.meets
    {pMain pSize pPass pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages.body pSize pPass))
    (hSize : P[pSize]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset))
    (hPass : P[pPass]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaPass.body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell.body pSetup pOffset pErase pRank))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body)
    (hErase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut base maskBase work U d : ℕ}
    (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^L*U : ℕ) : ℤ) ≤ lim.word)
    (hread : _root_.ThreeSum.LightZetaCell.TableAt μ base cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+7 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cut,base,maskBase,work] μ (_root_.ThreeSum.LightZetaStages.time L cut)
      (fun _ μ' => _root_.ThreeSum.LightZetaStages.StoredThrough μ' base cut f L ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase base ((L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut)) := by sorry
