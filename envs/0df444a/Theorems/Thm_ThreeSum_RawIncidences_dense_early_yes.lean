-- Prove2me | Theorems.Thm_ThreeSum_RawIncidences_dense_early_yes
-- name    : ThreeSum.RawIncidences.dense_early_yes
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:26:22.595988+00:00
-- url     : https://prove2.me/theorems/d8c3d269-df49-4fc9-9b78-0bbc8d2bad72
-- title:
--   Excess guarded incidence mass certifies a genuine 3SUM witness
-- statement:
--   Let $T$ be a finite set of triples in finite index types with decidable equality, with integer values $a,b,c$, and put $\Delta(i,j,k)=c(k)-b(j)-a(i)$. Fix natural $h,J$, integers $P>0,d$, and a finite auxiliary modulus set $A$. Assume the global encoding modulus $M\ge4P$, and every nonzero $\Delta(t)$, $t\in T$, fails divisibility by some element of $A$.
--
--   Let $F=\sum_{t\in T,\,P\mid\Delta(t)}|\{\ell\in A:\ell\nmid\Delta(t)\}|$, let $C=(\operatorname{scheduleSize}(h)\operatorname{localBucketCap}(h)^2)^J$, and let $R$ count the guarded radix witnesses over $T$, including their signed lifts, at shift $d$. Then
--   $$
--   CF<R\quad\Longrightarrow\quad\exists t\in T:\Delta(t)=0.
--   $$
--   This justifies accepting when the actual guarded incidence mass exceeds the weighted false-incidence threshold.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/RawIncidences.lean#L400-L433

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

universe u_1 u_2 u_3

theorem ThreeSum.RawIncidences.dense_early_yes : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J : Nat} {P d : Int}
  (T : Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)) (a : α → Int)
  (b : β → Int) (c : γ → Int) (aux : Finset.{0} Int)
  (hP : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) P)
  (hguard :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) P)
      (ThreeSum.GlobalEncoding.globalModulus h J))
  (hsep :
    ∀ (t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ),
      @Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3}
          (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
          (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ))
          (@SetLike.instMembership.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3}
            (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ))
            (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
            (@Finset.instSetLike.{max (max u_1 u_2) u_3} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)))
          T t →
        @Ne.{1} Int (@ThreeSum.RawIncidences.difference.{u_1, u_2, u_3} α β γ a b c t)
            (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          ∃ (l : Int),
            And
              (@Membership.mem.{0, 0} Int (Finset.{0} Int)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int (@Finset.instSetLike.{0} Int)) aux l)
              (Not (@Dvd.dvd.{0} Int Int.instDvd l (@ThreeSum.RawIncidences.difference.{u_1, u_2, u_3} α β γ a b c t))))
  (hlarge :
    @LT.lt.{0} Nat instLTNat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.GlobalEncoding.representationCap h J)
        (@ThreeSum.Arithmetic.weightedFalseCount.{max (max u_1 u_2) u_3}
          (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ) T
          (@ThreeSum.RawIncidences.difference.{u_1, u_2, u_3} α β γ a b c) aux P))
      (@ThreeSum.RawIncidences.rawMass.{u_1, u_2, u_3} α β γ h J P d T a b c)),
  ∃ (t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ),
    And
      (@Membership.mem.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3}
        (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
        (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ))
        (@SetLike.instMembership.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3}
          (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ))
          (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
          (@Finset.instSetLike.{max (max u_1 u_2) u_3} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)))
        T t)
      (@Eq.{1} Int (@ThreeSum.RawIncidences.difference.{u_1, u_2, u_3} α β γ a b c t)
        (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := by
  sorry
