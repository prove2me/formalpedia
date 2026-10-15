-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_heavyPairEvent_bound
-- name    : ThreeSum.HashFamily.heavyPairEvent_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:18:47.764781+00:00
-- url     : https://prove2.me/theorems/fb023b85-40c6-4dd9-97a8-149b73782045
-- title:
--   Heavy buckets remove at most a quarter of a prescribed hash-pair fiber
-- statement:
--   Let $\alpha$ be a finite coordinate set and $K$ a finite field of cardinality $q$. For a weight assignment $w:\alpha\times\{0,1\}\to K$, define $H_w(u)=\sum_{i\in\alpha}w(i,u_i)$. Fix distinct binary words $s,t$, arbitrary targets $a,b\in K$, and a finite set $V$ of binary words with $t\notin V$. Let $B$ be a natural number satisfying $4(q+|V|)\le Bq$. For
--   $$E=\{w:H_w(s)=a,\ H_w(t)=b,\ |\{u\in V:H_w(u)=a\}|>B\},$$
--   one has
--   $$4q^2|E|\le q^{2|\alpha|}.$$
--
--   This uniform counting bound controls the loss caused by discarding an oversized bucket, even when $s$ itself belongs to $V$ or the two targets coincide.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L677-L698

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
import Theorems.Thm_ThreeSum_HashFamily_loadedPairMass_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.HashFamily.heavyPairEvent_bound : ∀ {α : Type u_1} {K : Type u_2} [inst : Fintype.{u_1} α] [inst_1 : DecidableEq.{u_1 + 1} α] [inst_2 : Field.{u_2} K]
  [inst_3 : Fintype.{u_2} K] [inst_4 : DecidableEq.{u_2 + 1} K] {s t : α → Bool} (hst : @Ne.{u_1 + 1} (α → Bool) s t)
  (a b : K) (vertices : Finset.{u_1} (α → Bool))
  (hcross :
    ∀ (u : α → Bool),
      @Membership.mem.{u_1, u_1} (α → Bool) (Finset.{u_1} (α → Bool))
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (α → Bool)) (α → Bool)
            (@Finset.instSetLike.{u_1} (α → Bool)))
          vertices u →
        @Ne.{u_1 + 1} (α → Bool) u t)
  (B : Nat)
  (hB :
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fintype.card.{u_2} K inst_3)
          (@Finset.card.{u_1} (α → Bool) vertices)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) B (@Fintype.card.{u_2} K inst_3))),
  @LE.le.{0} Nat instLENat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@Fintype.card.{u_2} K inst_3) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@Finset.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
        (@ThreeSum.HashFamily.heavyPairEvent.{u_1, u_2} α K inst inst_1 inst_2 inst_3 inst_4 s t a b vertices B)))
    (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
      (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
        (fun (a b : Prod.{u_1, 0} α Bool) => @instDecidableEqProd.{u_1, 0} α Bool inst_1 instDecidableEqBool a b)
        (@instFintypeProd.{u_1, 0} α Bool inst Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_3)) := by
  sorry
