-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_raw_second_moment_five
-- name    : ThreeSum.HashFamily.raw_second_moment_five
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:39:29.708187+00:00
-- url     : https://prove2.me/theorems/8a6eb91b-22a3-461e-a804-e5f1fba69774
-- title:
--   A five-times-density second-moment bound for concrete hashes
-- statement:
--   Let $K$ be a finite field of size $p$, $\alpha$ a finite coordinate set, and $E$ a finite edge set. Each edge has binary words $(\ell_e,r_e)$, with distinct ordered pairs and $\ell_e\ne r_f$ for all $e,f$. An edge's bad partners share its left endpoint, right endpoint, or coordinatewise equality mask. Suppose every bad-partner set has size at most $B\le3p$, and $|E|\le p^2$. For $w\in\Omega=K^{\alpha\times\{0,1\}}$, put $H_w(s)=\sum_iw(i,s_i)$ and $X_w=|\{e:H_w(\ell_e)=a,\ H_w(r_e)=b\}|$, where $a,b\in K$. Then
--   $$
--   p^2\sum_{w\in\Omega}X_w^2\le5|E|\,|\Omega|.
--   $$
--   This supplies the coarse second-moment estimate for the actual one-hot hash family.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L562-L588

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
import Theorems.Thm_ThreeSum_HashFamily_raw_second_moment


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2 u_3

theorem ThreeSum.HashFamily.raw_second_moment_five : ∀ {α : Type u_1} {K : Type u_2} {E : Type u_3} [inst : Fintype.{u_3} E] [DecidableEq.{u_3 + 1} E]
  [inst_2 : Fintype.{u_1} α] [inst_3 : DecidableEq.{u_1 + 1} α] [inst_4 : Field.{u_2} K] [inst_5 : Fintype.{u_2} K]
  [inst_6 : DecidableEq.{u_2 + 1} K] (left right : E → α → Bool)
  (hinj :
    @Function.Injective.{u_3 + 1, u_1 + 1} E (Prod.{u_1, u_1} (α → Bool) (α → Bool)) fun (e : E) =>
      @Prod.mk.{u_1, u_1} (α → Bool) (α → Bool) (left e) (right e))
  (hcross : ∀ (e f : E), @Ne.{u_1 + 1} (α → Bool) (left e) (right f)) (B : Nat)
  (hB :
    ∀ (e : E),
      @LE.le.{0} Nat instLENat
        (@Finset.card.{u_3} E (@ThreeSum.HashFamily.badPartners.{u_1, u_3} α E inst inst_2 left right e)) B)
  (hBp :
    @LE.le.{0} Nat instLENat B
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fintype.card.{u_2} K inst_5)))
  (hEp :
    @LE.le.{0} Nat instLENat (@Fintype.card.{u_3} E inst)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@Fintype.card.{u_2} K inst_5) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (a b : K),
  @LE.le.{0} Nat instLENat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@Fintype.card.{u_2} K inst_5) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (∑ w : Prod.{u_1, 0} α Bool → K,
        @HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@ThreeSum.HashFamily.incidenceCount.{max u_2 u_1, u_3} (Prod.{u_1, 0} α Bool → K) E inst
            (fun (a b : Prod.{u_1, 0} α Bool → K) =>
              @Fintype.decidablePiFintype.{u_2, u_1} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
                (fun (a : Prod.{u_1, 0} α Bool) => inst_6) (@instFintypeProd.{u_1, 0} α Bool inst_2 Bool.fintype) a b)
            (fun (e : E) =>
              @ThreeSum.HashFamily.pairEvent.{u_1, u_2} α K inst_2 inst_3 inst_4 inst_5 inst_6 (left e) (right e) a b)
            w)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (@Fintype.card.{u_3} E inst))
      (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
        (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
          (fun (a b : Prod.{u_1, 0} α Bool) => @instDecidableEqProd.{u_1, 0} α Bool inst_3 instDecidableEqBool a b)
          (@instFintypeProd.{u_1, 0} α Bool inst_2 Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_5))) := by
  sorry
