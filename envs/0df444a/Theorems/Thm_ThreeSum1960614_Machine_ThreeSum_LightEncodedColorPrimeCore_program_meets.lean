-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightEncodedColorPrimeCore_program_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program_meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:46:59.669811+00:00
-- url     : https://prove2.me/theorems/15aba28a-c58e-4092-b70f-05ce999384cc
-- title:
--   Complete common-prime construction from original owner scores
-- statement:
--   Let positive prime-window and band-width controls $y,g$ and radix $M$ be given. Suppose the three stored source arrays are bounded by $U$, owner records have Boolean flags and valid flagged bands, and all inputs precede the free address. Assume $(4y)^{d(M,y)+1}$ is at most the supplied maximum modulus, and the stated space, word, address, and call-depth bounds hold. The closed core program returns the exact modulus after the prescribed depth, stores every specified prefix-modulus field, and preserves the original prefix within its stated time.
--
--   Executes the full deterministic common-prime chain without supplied prime-quality data. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightEncodedColorPrimeCore.lean#L55-L171

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
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
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing

namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeChain
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeChain
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimePool.Procs
end ThreeSum1960614.Machine.ThreeSum.LightPrimePool.Procs


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.EncodedColorPrimeData
end ThreeSum.EncodedColorPrimeData
namespace ThreeSum.LightEncodedColorPrimeCore
end ThreeSum.LightEncodedColorPrimeCore
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightEncodedColorPrimeCore
open _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.EncodedColorPrimeData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
set_option maxHeartbeats 2600000
set_option maxRecDepth 13000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs M y free maxMod U : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program_meets (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y) (hg : 0 < g)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free)
    (hspace : _root_.ThreeSum.LightEncodedColorPrimeCore.space free maxMod g M y U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightEncodedColorPrimeCore.word maxMod nA nB nC g rs.length M y U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+9 ≤ lim.depth)
    (hrecords : _root_.ThreeSum1960614.Machine.Light.Seg μ recs (_root_.ThreeSum.BandCandidateRows.cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hmax : (4*y)^(_root_.ThreeSum.LightBandPrimeDepth.depth M y+1) ≤ maxMod) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeCore.program 23 d [a,b,c,nA,nB,nC,g,recs,rs.length,M,y,free] μ
      (_root_.ThreeSum.LightEncodedColorPrimeCore.time maxMod g rs.length M y U)
      (fun result ν =>
        result=(_root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData.Stored ν free M y
          (_root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g
            (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by sorry
