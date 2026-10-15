-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingSuffixQuery_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:32:18.820044+00:00
-- url     : https://prove2.me/theorems/3aa16027-fb9d-4314-80ee-787bff87ab02
-- title:
--   Exact suffix-local sparse query
-- statement:
--   Let a width-$V$ suffix at offset $o$ fit inside a width-$W$ ground set. Let integer functions $f,g$ be bounded by $B,D$ through cutoff $c\le W$, with stage $s\le W$ stored. For query subset $Q$ and prefixes disjoint from its lift, assume both prefix unions fit cutoff; threshold $t\le|Q|+1$; box cutoff at most $|Q|$ and at least $|Q|-t$; exact suffix-box storage; and the stated table, mask, Pascal, word, and depth bounds. The closed program returns the Möbius sum of the product of the two stage functions on the lifted query within its stated time, preserving other cells below work scratch.
--
--   Connects actual suffix-local boxes and explicit leaves to the original sparse-query value. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightReportingSuffixQuery.lean#L90-L200

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCanonicalBoxSum_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingSuffixExplicit_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSign_meets
import Theorems.Thm_ThreeSum_SparseBoxes_mem_explicitLeaves
import Theorems.Thm_ThreeSum_SparseBoxes_sparse_query_identity
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixQuery
end ThreeSum.LightReportingSuffixQuery
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingSuffixQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open scoped _root_.BigOperators
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program_meets
    {μ : ℕ → ℤ} {W V offset cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase+(V+1)*_root_.ThreeSum.SubsetAddress.downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.LightSparseQuery.queryItems Q.card t ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (_root_.ThreeSum.LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hboxCut : boxCut ≤ Q.card) (hflags : Q.card-t ≤ boxCut)
    (hdisjL : Disjoint preL (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q)) (hdisjR : Disjoint preR (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q))
    (hcardL : (preL ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : _root_.ThreeSum.LightBoxStages.StoredThrough μ boxBase boxCut
      (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) V)
    (hd : d+W+9 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program 28 d
      [W,cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,V,2^offset,
        Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,baseL,baseR,boxCut,boxBase,maskBase,work] μ (_root_.ThreeSum.LightReportingSuffixQuery.time W V Q.card t)
      (fun r μ' =>
        r = _root_.ThreeSum.Subset.mobius (fun S => _root_.ThreeSum.SubsetStages.stageValue f stage (preL ∪ S)*
          _root_.ThreeSum.SubsetStages.stageValue g stage (preR ∪ S)) (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work maskBase (_root_.ThreeSum.LightSparseQuery.queryItems Q.card t)) := by sorry
