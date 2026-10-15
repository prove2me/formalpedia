-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalKeys_Procs_meets
-- name    : ThreeSum1960614.Machine.ThreeSum.LightLocalKeys.Procs.meets
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:14:19.299413+00:00
-- url     : https://prove2.me/theorems/10fb9614-daad-4f81-9db3-3d993a166289
-- title:
--   The complete occurrence-by-output local key array
-- statement:
--   Let stored masks lie below $2^L$, and let each of $R$ selected map rows have two width-$L$ coefficient orientations bounded by $U$. Assume input segments precede the $Rn$ output, the output ends before scratch, and the concrete procedure interface and stated space, word, address, and depth bounds hold. The routine writes at position $(j,i)$ the difference of the true- and false-orientation one-hot evaluations for mask $i$, in its specified time, preserving the preceding memory.
--
--   Constructs signed local output keys in exact occurrence order. This supports the complete deterministic integer 3SUM runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightLocalKeys.lean#L45-L129

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
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
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalKeyRow_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalKeys
end ThreeSum.LightLocalKeys
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalKeys
end ThreeSum1960614.Machine.ThreeSum.LightLocalKeys

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLocalKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalKeys

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalKeys.Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalKeys.Procs P pMain)
    {μ : ℕ → ℤ} {L masks n maps rows dst free U : ℕ}
    (mask : ℕ → ℕ) (wFalse wTrue : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+3 ≤ lim.depth)
    (hspace : _root_.ThreeSum.LightLocalKeyRow.space free L n ≤ lim.space)
    (hmasks : masks+n ≤ dst) (hmaps : maps+rows*(2*L) ≤ dst) (hdst : dst+rows*n ≤ free)
    (hword : (_root_.ThreeSum.LightLocalKeys.word L U rows : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i)=(mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hreadFalse : ∀ j < rows, ∀ i < L, μ (maps+j*(2*L)+i)=(wFalse j i : ℤ))
    (hreadTrue : ∀ j < rows, ∀ i < L, μ (maps+j*(2*L)+L+i)=(wTrue j i : ℤ))
    (hboundFalse : ∀ j < rows, ∀ i < L, wFalse j i ≤ U)
    (hboundTrue : ∀ j < rows, ∀ i < L, wTrue j i ≤ U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,masks,n,maps,rows,dst,free] μ (_root_.ThreeSum.LightLocalKeys.time L n rows)
      (fun _ ν =>
        (∀ j < rows, ∀ i < n, ν (dst+j*n+i)=
          (_root_.ThreeSum.OneHotMask.eval (wTrue j) (fun _ => 0) L (mask i) : ℤ)-
          (_root_.ThreeSum.OneHotMask.eval (wFalse j) (fun _ => 0) L (mask i) : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by sorry
