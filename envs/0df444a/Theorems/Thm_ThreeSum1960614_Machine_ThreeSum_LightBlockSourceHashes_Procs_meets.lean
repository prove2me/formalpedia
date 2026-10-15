-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceHashes_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:30:10.206743+00:00
-- url     : https://prove2.me/theorems/11980c68-86c3-451d-a661-fd34a0aa052c
-- title:
--   Constructing both positional source hash arrays
-- statement:
--   For $J$ width-$L$ blocks and radix $p\ge1$, let stored occurrence selections index bounded coefficient pairs, and let $n$ stored masks be below $2^{JL}$. Assume their read predicates, ordered coefficient and raw-hash outputs, and full helper, space, word, and depth requirements. The program writes the left and right one-hot evaluations using the flattened positional coefficients, retains the exact coefficient rows, and preserves memory below the coefficient destination within its stated time.
--
--   This hash contract materializes both semantic block endpoints from the selected local coefficient rows.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightBlockSourceHashes.lean#L50-L141

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockCoefficients_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskHashes_meets
import Theorems.Thm_ThreeSum_BlockCoefficientRows_rows_flat

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.LightBlockSourceHashes
end ThreeSum.LightBlockSourceHashes
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBlockSourceHashes
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceHashes.Procs P pMain)
    {μ : ℕ → ℤ} {J L p occ maps coeff0 coeff1 masks rawLeft rawRight n work U M : ℕ}
    (sel mask : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hd : d+J*L+2 ≤ lim.depth) (hspace : _root_.ThreeSum.LightBlockSourceHashes.space work J L ≤ lim.space)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*L*M ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*L ≤ coeff1)
    (hc1 : coeff1+J*L ≤ rawLeft) (hleft : rawLeft+n ≤ rawRight)
    (hright : rawRight+n ≤ work) (hword : (_root_.ThreeSum.LightBlockSourceHashes.word J L p U : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^(J*L)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [J,L,p,occ,maps,coeff0,coeff1,masks,rawLeft,rawRight,n,work]
      μ (_root_.ThreeSum.LightBlockSourceHashes.time J L n) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) =
          (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (rawRight+i) =
          (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w1) (_root_.ThreeSum.BlockCoefficientRows.flat J L p sel w0) (J*L) (mask i) : ℤ)) ∧
        _root_.ThreeSum.LightBlockCoefficients.Rows ν coeff0 coeff1 L p sel w0 w1 J ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν coeff0) := by sorry
