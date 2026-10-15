-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightModuloCounts_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightModuloCounts.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:16:50.231134+00:00
-- url     : https://prove2.me/theorems/eec20936-fdfc-42a9-94d3-413362f70ad1
-- title:
--   Execution of exact modular triple counting
-- statement:
--   Let $p>0$, integer input arrays A,B,C of lengths $n_A,n_B,n_C\le N$ and magnitude bound $U$ be stored before free address $f$ in memory $\mu$. Let $\lambda,P,d$ be limits, program and depth with the modular-count wrapper, capacity, signed residues, histogram/fill, cyclic product, lookup sum and concrete Karatsuba closures present. Assume addresses fit words, the exact counting space/word budgets fit and $d+\lceil\log_2p\rceil+3$ is allowed. Then the call returns
--
--   $$|\{(i,j,k):i<n_A,\ j<n_B,\ k<n_C,\ p\mid C_k-B_j-A_i\}|,$$
--
--   within its prescribed time, preserving every cell below $f$.
--
--   This supplies actual fast modular counts used by prime selection and weighted false-score computation.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightModuloCounts.lean#L50-L200

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCapacity_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCyclic_correlation_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLookupSum_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightResidueHistogram_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightResidues_residues_ends
import Theorems.Thm_ThreeSum_Histograms_tripleMass_eq_histogram

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightModuloCounts
end ThreeSum.LightModuloCounts
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
end ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightModuloCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightModuloCounts.meets {pMain pCapacity pHist pCyclic pResidues pEmod
    pHistogram pMultiply pHalf pLinear pFill pLookup : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts.body pCapacity pHist pCyclic pResidues pLookup))
    (hcap : P[pCapacity]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightCapacity.body)
    (hhist : P[pHist]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.body pResidues pHistogram))
    (hres : P[pResidues]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody pEmod))
    (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    (hcount : P[pHistogram]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody pFill))
    (hcyclic : P[pCyclic]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.body pMultiply pLinear))
    (K : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    (hlookup : P[pLookup]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightLookupSum.body)
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : _root_.ThreeSum.LightModuloCounts.space free p N U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightModuloCounts.word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ (_root_.ThreeSum.LightModuloCounts.time p nA nB nC U)
      fun r μ' =>
        r = (_root_.ThreeSum.ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          _root_.ThreeSum1960614.Machine.Light.Kept μ μ' free := by sorry
