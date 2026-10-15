-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_trimmedPairEvent_bound
-- name    : ThreeSum.HashFamily.trimmedPairEvent_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:39:44.597989+00:00
-- url     : https://prove2.me/theorems/15a0c822-1655-4aba-8aec-855e03c66778
-- title:
--   Two bucket caps retain at least half of every pair event
-- statement:
--   Let $K$ be a finite field of size $p$, $\alpha$ a finite coordinate set, and $s\ne t$ binary words on $\alpha$. For arbitrary targets $a,b\in K$, take finite word sets $L,R$ with $t\notin L$ and $s\notin R$. Choose a natural cap $B$ satisfying $4(p+|L|)\le Bp$ and $4(p+|R|)\le Bp$. For $H_w(u)=\sum_iw(i,u_i)$, let $T$ contain the weights with $H_w(s)=a$, $H_w(t)=b$, at most $B$ words of $L$ hashing to $a$, and at most $B$ words of $R$ hashing to $b$. Then
--   $$
--   |K^{\alpha\times\{0,1\}}|\le2p^2|T|.
--   $$
--   Thus separable trimming preserves at least half of the raw pair event, uniformly in the target residues.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L711-L742

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_HashFamily_hashMap_surjective
import Theorems.Thm_ThreeSum_HashFamily_heavyPairEvent_bound
import Theorems.Thm_ThreeSum_HashFamily_linear_fiber_card


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.HashFamily.trimmedPairEvent_bound : ∀ {α : Type u_1} {K : Type u_2} [inst : Fintype.{u_1} α] [inst_1 : DecidableEq.{u_1 + 1} α] [inst_2 : Field.{u_2} K]
  [inst_3 : Fintype.{u_2} K] [inst_4 : DecidableEq.{u_2 + 1} K] {s t : α → Bool} (hst : @Ne.{u_1 + 1} (α → Bool) s t)
  (a b : K) (leftVertices rightVertices : Finset.{u_1} (α → Bool))
  (hL :
    ∀ (u : α → Bool),
      @Membership.mem.{u_1, u_1} (α → Bool) (Finset.{u_1} (α → Bool))
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (α → Bool)) (α → Bool)
            (@Finset.instSetLike.{u_1} (α → Bool)))
          leftVertices u →
        @Ne.{u_1 + 1} (α → Bool) u t)
  (hR :
    ∀ (u : α → Bool),
      @Membership.mem.{u_1, u_1} (α → Bool) (Finset.{u_1} (α → Bool))
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (α → Bool)) (α → Bool)
            (@Finset.instSetLike.{u_1} (α → Bool)))
          rightVertices u →
        @Ne.{u_1 + 1} (α → Bool) u s)
  (B : Nat)
  (hBL :
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fintype.card.{u_2} K inst_3)
          (@Finset.card.{u_1} (α → Bool) leftVertices)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) B (@Fintype.card.{u_2} K inst_3)))
  (hBR :
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fintype.card.{u_2} K inst_3)
          (@Finset.card.{u_1} (α → Bool) rightVertices)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) B (@Fintype.card.{u_2} K inst_3))),
  @LE.le.{0} Nat instLENat
    (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
      (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
        (fun (a b : Prod.{u_1, 0} α Bool) => @instDecidableEqProd.{u_1, 0} α Bool inst_1 instDecidableEqBool a b)
        (@instFintypeProd.{u_1, 0} α Bool inst Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_3))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@Fintype.card.{u_2} K inst_3) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@Finset.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
        (@ThreeSum.HashFamily.trimmedPairEvent.{u_1, u_2} α K inst inst_1 inst_2 inst_3 inst_4 s t a b leftVertices
          rightVertices B))) := by
  sorry
