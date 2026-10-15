-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceRetainedStages_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:27:24.773816+00:00
-- url     : https://prove2.me/theorems/804f57aa-4b65-4ab8-a001-6283263d75e9
-- title:
--   Execution of retained-source suffix transforms
-- statement:
--   Let width $L$, cutoff $c\le L$, positive modulus $m$, endpoint map $e$ with $|e(S)|\le E$ for $|S|\le c$, Boolean flag map $\phi$, and histogram $H(r)\le B$ for $r<m$ be given. Suppose memory stores their exact compact endpoint/flag rows and histogram before transform base $b$. The $(L+1)D(L,c)$ transform cells end before a length-$D(L,c)$ mask buffer, which ends before scratch. Assume addresses fit words, the exact transform space/word budgets fit and depth $d+L+8$ is allowed. With the literal source-stage closure, it constructs all suffix-zeta stages of
--
--   $$F(S)=\begin{cases}H(e(S)\bmod m),&\phi(S)=1,\\0,&\phi(S)=0,\end{cases}$$
--
--   meets its prescribed time and preserves every cell below $b$.
--
--   This turns retained endpoint/flag data and actual input histograms into the exact compact source transforms.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightSourceRetainedStages.lean#L60-L122

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
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceGather_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightZetaStages_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSourceRetainedStages
end ThreeSum.LightSourceRetainedStages
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages
end ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceRetainedStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs.meets {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs P pMain)
    {μ : ℕ → ℤ} {raw flags table base m work L cut maskBase E B : ℕ}
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+8 ≤ lim.depth)
    (hm : 0 < m) (hcut : cut ≤ L)
    (hraw : raw+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ base) (hflags : flags+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ base)
    (htable : table+m ≤ base) (hdata : base+(L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hspace : _root_.ThreeSum.LightSourceRetainedStages.space work L E ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceRetainedStages.word L m E B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap L cut,
      μ (raw+i) = endpoint (_root_.ThreeSum.SourceTableLayout.setAt L cut i))
    (hrawBound : ∀ S, S.card ≤ cut → |endpoint S| ≤ (E : ℤ))
    (hflagRead : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap L cut,
      μ (flags+i) = (flag (_root_.ThreeSum.SourceTableLayout.setAt L cut i) : ℤ))
    (hflagBound : ∀ S, S.card ≤ cut → flag S ≤ 1)
    (hhistRead : ∀ r < m, μ (table+r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [raw,flags,table,base,m,work,L,cut,maskBase,_root_.ThreeSum.SubsetAddress.downsetCap L cut]
      μ (_root_.ThreeSum.LightSourceRetainedStages.time L cut E) (fun _ ν =>
        _root_.ThreeSum.LightZetaStages.StoredThrough ν base cut (_root_.ThreeSum.LightSourceRetainedStages.source m endpoint flag hist) L ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν base) := by sorry
