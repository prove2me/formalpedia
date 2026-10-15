-- Prove2me | Theorems.Thm_ThreeSum_RawReporting_word_children
-- name    : ThreeSum.RawReporting.word_children
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:54:32.22677+00:00
-- url     : https://prove2.me/theorems/af5648f8-47bb-4de6-93cf-708ac8751937
-- title:
--   Every raw reporting word follows an allowed balanced child
-- statement:
--   Let $\alpha,\beta,\gamma$ be finite index types with decidable equality, and let $I$ be a finite set of raw items for block parameters $h,J$. A raw item contains an original index triple, a lift label, and local edge choices. Fix a wanted label $w=(a,\ell,q)$, and suppose $r\in I$ has this label. For each block $j<J$, let $Q_j\subseteq\{0,\ldots,512h-1\}$ be the $2h$-element output subset in $q$, and let $S_j(r)$ be the left subset recorded in the partition word of $r$. Then
--   $$S_j(r)\in\mathcal C_j(q),\qquad \mathcal C_j(q)=\{S\subseteq Q_j:|S|=h\},$$
--   where the children are listed in deterministic colex order.
--
--   This connects every raw witness to a legal edge of the reporting tree.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/RawReporting.lean#L104-L118

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
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
import Theorems.Thm_ThreeSum_RawReporting_partitionWord_length


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences

universe u_1 u_2 u_3

theorem ThreeSum.RawReporting.word_children : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J : Nat}
  (I : Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ))
  (w : ThreeSum.RawReporting.Wanted.{u_1} h J α) (r : ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ)
  (hr :
    @Membership.mem.{max (max u_1 u_2) u_3, max (max u_3 u_2) u_1}
      (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ)
      (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ))
      (@SetLike.instMembership.{max (max u_1 u_2) u_3, max (max u_1 u_2) u_3}
        (Finset.{max (max u_3 u_2) u_1} (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ))
        (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ)
        (@Finset.instSetLike.{max (max u_1 u_2) u_3} (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ)))
      (@ThreeSum.RawReporting.domain.{u_1, u_2, u_3} α β γ inst h J I w) r)
  (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j J),
  @Membership.mem.{0, 0}
    (Finset.{0}
      (Fin
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
    (List.{0}
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
    (@List.instMembership.{0}
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
    (@ThreeSum.RawReporting.children h J
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput h J)
        (@Prod.snd.{u_1, 0} α
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput h J))
          w))
      j)
    (@GetElem.getElem.{0, 0, 0}
      (List.{0}
        (Finset.{0}
          (Fin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
      Nat
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
      (fun
          (as :
            List.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
          (i : Nat) =>
        @LT.lt.{0} Nat instLTNat i
          (@List.length.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            as))
      (@List.instGetElemNatLtLength.{0}
        (Finset.{0}
          (Fin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
      (@ThreeSum.RawReporting.word.{u_1, u_2, u_3} h J α β γ r) j
      (@Eq.mpr.{0}
        (@LT.lt.{0} Nat instLTNat j
          (@List.length.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            (@ThreeSum.RawReporting.word.{u_1, u_2, u_3} h J α β γ r)))
        (@LT.lt.{0} Nat instLTNat j
          (@List.length.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            (@ThreeSum.RawReporting.partitionWord h J
              (@Prod.fst.{0, 0} (ThreeSum.RawIncidences.ChoiceTuple h J)
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@Sigma.snd.{max (max u_1 u_2) u_3, 0} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                  (fun (_t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ) =>
                    ThreeSum.RawIncidences.Witness h J)
                  r)))))
        (@id.{0}
          (@Eq.{1} Prop
            (@LT.lt.{0} Nat instLTNat j
              (@List.length.{0}
                (Finset.{0}
                  (Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                (@ThreeSum.RawReporting.word.{u_1, u_2, u_3} h J α β γ r)))
            (@LT.lt.{0} Nat instLTNat j
              (@List.length.{0}
                (Finset.{0}
                  (Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                (@ThreeSum.RawReporting.partitionWord h J
                  (@Prod.fst.{0, 0} (ThreeSum.RawIncidences.ChoiceTuple h J)
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@Sigma.snd.{max (max u_1 u_2) u_3, 0} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                      (fun (_t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ) =>
                        ThreeSum.RawIncidences.Witness h J)
                      r))))))
          (@congrArg.{1, 1}
            (List.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
            Prop (@ThreeSum.RawReporting.word.{u_1, u_2, u_3} h J α β γ r)
            (@ThreeSum.RawReporting.partitionWord h J
              (@Prod.fst.{0, 0} (ThreeSum.RawIncidences.ChoiceTuple h J)
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@Sigma.snd.{max (max u_1 u_2) u_3, 0} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                  (fun (_t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ) =>
                    ThreeSum.RawIncidences.Witness h J)
                  r)))
            (fun
                (_a :
                  List.{0}
                    (Finset.{0}
                      (Fin
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))) =>
              @LT.lt.{0} Nat instLTNat j
                (@List.length.{0}
                  (Finset.{0}
                    (Fin
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                  _a))
            (@ThreeSum.RawReporting.word.eq_1.{u_1, u_2, u_3} h J α β γ r)))
        (@Eq.mpr.{0}
          (@LT.lt.{0} Nat instLTNat j
            (@List.length.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
              (@ThreeSum.RawReporting.partitionWord h J
                (@Prod.fst.{0, 0} (ThreeSum.RawIncidences.ChoiceTuple h J)
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@Sigma.snd.{max (max u_1 u_2) u_3, 0} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                    (fun (_t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ) =>
                      ThreeSum.RawIncidences.Witness h J)
                    r)))))
          (@LT.lt.{0} Nat instLTNat j J)
          (@id.{0}
            (@Eq.{1} Prop
              (@LT.lt.{0} Nat instLTNat j
                (@List.length.{0}
                  (Finset.{0}
                    (Fin
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                  (@ThreeSum.RawReporting.partitionWord h J
                    (@Prod.fst.{0, 0} (ThreeSum.RawIncidences.ChoiceTuple h J)
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@Sigma.snd.{max (max u_1 u_2) u_3, 0} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                        (fun (_t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ) =>
                          ThreeSum.RawIncidences.Witness h J)
                        r)))))
              (@LT.lt.{0} Nat instLTNat j J))
            (@congrArg.{1, 1} Nat Prop
              (@List.length.{0}
                (Finset.{0}
                  (Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                (@ThreeSum.RawReporting.partitionWord h J
                  (@Prod.fst.{0, 0} (ThreeSum.RawIncidences.ChoiceTuple h J)
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@Sigma.snd.{max (max u_1 u_2) u_3, 0} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                      (fun (_t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ) =>
                        ThreeSum.RawIncidences.Witness h J)
                      r))))
              J (fun (_a : Nat) => @LT.lt.{0} Nat instLTNat j _a)
              (@ThreeSum.RawReporting.partitionWord_length h J
                (@Prod.fst.{0, 0} (ThreeSum.RawIncidences.ChoiceTuple h J)
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@Sigma.snd.{max (max u_1 u_2) u_3, 0} (ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ)
                    (fun (_t : ThreeSum.RawIncidences.Original.{u_1, u_2, u_3} α β γ) =>
                      ThreeSum.RawIncidences.Witness h J)
                    r)))))
          hj))) := by
  sorry
