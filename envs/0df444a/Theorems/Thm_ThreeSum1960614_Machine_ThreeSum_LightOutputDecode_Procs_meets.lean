-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecode_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:27:20.872254+00:00
-- url     : https://prove2.me/theorems/d50195db-08df-4c19-ad9b-016ff332bbaf
-- title:
--   Execution of complete output-record decoding
-- statement:
--   Let $T,M\ge1$, $k\le V$ and $J,U\in\mathbb N$. Suppose a length-$M$ mask table $f(s)\le U$ is stored in memory $\mu$ before output base $b$, with $b+2J\le w$ before scratch. Let $\lambda,P,d$ be run limits, program and depth, and let the literal procedure record identify the output decoder and its division/digit callees. Assume addresses fit words, the exact decoder space and word budgets fit and $d+2$ is strictly below the call limit. For the forward base-$TM$ digits $z_j$ of $k$, the procedure writes
--
--   $$\nu(b+j)=\lfloor z_j/M\rfloor,\qquad\nu(b+J+j)=f(z_j\bmod M),$$
--
--   returns the occurrence-only radix-$T$ code, meets its stated time and preserves cells below $b$.
--
--   This connects every physical global output to its original occurrence and mask rows.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightOutputDecode.lean#L64-L197

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
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
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeDigits_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeStep_meets
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_getD_reverse

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightOutputDecode
end ThreeSum.LightOutputDecode
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecode
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecode

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightOutputDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J T M masks dst work V U : ℕ} {f : ℕ → ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hT : 1 ≤ T) (hM : 1 ≤ M) (hk : k ≤ V)
    (hmask : masks+M ≤ dst) (hsep : dst+J+J ≤ work)
    (hspace : _root_.ThreeSum.LightOutputDecode.space work V ≤ lim.space)
    (hword : (_root_.ThreeSum.LightOutputDecode.word V T M J U : ℤ) ≤ lim.word)
    (hf : ∀ s < M, f s ≤ U) (hread : ∀ s < M, μ (masks+s)=(f s : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [k,J,T,M,masks,dst,work] μ (_root_.ThreeSum.LightOutputDecode.time J V)
      (fun r ν => r=(_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J k : ℤ) ∧
        (∀ j < J, ν (dst+j)=(((_root_.ThreeSum.OutputDecodeOrder.indices (T*M) J k).getD j 0/M : ℕ) : ℤ)) ∧
        (∀ j < J, ν (dst+J+j)=(f ((_root_.ThreeSum.OutputDecodeOrder.indices (T*M) J k).getD j 0%M) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by sorry
