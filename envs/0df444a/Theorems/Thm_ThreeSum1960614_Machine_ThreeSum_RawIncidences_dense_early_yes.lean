-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawIncidences_dense_early_yes
-- name    : ThreeSum1960614.Machine.ThreeSum.RawIncidences.dense_early_yes
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:58:18.079007+00:00
-- url     : https://prove2.me/theorems/a6762d36-e71b-4bed-8668-cad3d1d645bd
-- title:
--   A dense raw mass certifies an original zero
-- statement:
--   Let $h,J\in\mathbb N$, $P>0$ and $\delta\in\mathbb Z$. Let $T$ be a finite set of original triples over finite decidable index types, with integer maps $a,b,c$, and write $\Delta(t)=c(t_C)-b(t_B)-a(t_A)$. Let $A$ be a finite auxiliary-modulus set. Assume $4P$ is at most the global encoding modulus and every $t\in T$ with $\Delta(t)\ne0$ fails divisibility by at least one modulus in $A$. If
--
--   $$\operatorname{repCap}(h,J)\,\operatorname{weightedFalseCount}(T,\Delta,A,P)<\operatorname{rawMass}(h,J,P,\delta,T,a,b,c),$$
--
--   then $\Delta(t)=0$ for some $t\in T$.
--
--   This is the soundness bridge for the machine’s cumulative early-YES dense branch.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/RawIncidences.lean#L400-L433

import Aesop
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
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
import Theorems.Thm_ThreeSum_Arithmetic_early_yes
import Theorems.Thm_ThreeSum_LocalHashMoments_hitCount_cap
import Theorems.Thm_ThreeSum_Radix_mem_representations
import Theorems.Thm_ThreeSum_Radix_representations_card_le

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences

open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences

set_option maxRecDepth 8000
open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum1960614.Machine.ThreeSum.RawIncidences.dense_early_yes {h J : ℕ} {P d : ℤ} (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (aux : Finset ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hsep : ∀ t ∈ T, _root_.ThreeSum.RawIncidences.difference a b c t ≠ 0 → ∃ l ∈ aux, ¬l ∣ _root_.ThreeSum.RawIncidences.difference a b c t)
    (hlarge : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J * _root_.ThreeSum.Arithmetic.weightedFalseCount T (_root_.ThreeSum.RawIncidences.difference a b c) aux P <
      _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawMass h J P d T a b c) :
    ∃ t ∈ T, _root_.ThreeSum.RawIncidences.difference a b c t = 0 := by sorry
