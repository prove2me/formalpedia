-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBoxSum_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBoxSum.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:19:47.508912+00:00
-- url     : https://prove2.me/theorems/b7282e1f-40c7-4190-a19f-2c83ea575b37
-- title:
--   Summing an explicitly stored family of canonical boxes
-- statement:
--   Let $Q$ be a subset of a width-$L$ ground set and let a stored list contain subsets $U\subseteq Q$ of fixed size $t$, each with $|Q\setminus U|\le c\le L$. Suppose weights are bounded by $B$ through cutoff $c$, their box stages are stored, the concrete box-query interface and stated data/mask/Pascal allocations and depth bounds hold, and the accumulator bound $|\mathrm{list}|2^LB$ fits a word. The procedure returns the sum of the specified canonical-box values within its stated time and preserves memory below scratch.
--
--   Evaluates exactly the supplied canonical missing-set family with bounded signed accumulation. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBoxSum.lean#L59-L150

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
import Mathlib.Data.Finset.Max
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
import Mathlib.Tactic.Push
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightQueryBox_meets
import Theorems.Thm_ThreeSum_BoxBounds_boxSum_abs_le
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBoxSum
end ThreeSum.LightBoxSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBoxSum
end ThreeSum1960614.Machine.ThreeSum.LightBoxSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBoxSum
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBoxSum

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem ThreeSum1960614.Machine.ThreeSum.LightBoxSum.meets
    {pMain pBox pMinimum pLookup pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBoxSum.body pBox))
    (hBox : P[pBox]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryBox.body pMinimum pLookup))
    (hMinimum : P[pMinimum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskMinimum.body pPowers pErase))
    (hLookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.body pSize pAddress))
    (hSize : P[pSize]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress.body pSetup pOffset))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body)
    (hErase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut t maskBase base work B d : ℕ}
    (Q : Finset (Fin L)) (missing : List (Finset (Fin L))) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*(2^L*B) : ℕ) : ℤ) ≤ lim.word)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t ∧ (Q \ U).card ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : _root_.ThreeSum.LightBoxStages.StoredThrough μ base cut weight L)
    (hseg : _root_.ThreeSum1960614.Machine.Light.SegN μ maskBase (missing.map _root_.ThreeSum.SubsetAddress.subsetMask))
    (hd : d+L+7 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cut,Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,missing.length,maskBase,base,work]
      μ (_root_.ThreeSum.LightBoxSum.time L missing.length)
      (fun r μ' => r = (missing.map (_root_.ThreeSum.LightBoxSum.boxValue Q weight)).sum ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' work) := by sorry
