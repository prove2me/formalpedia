-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_badPartners_card_le
-- name    : ThreeSum.HashFamily.badPartners_card_le
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:41:41.67582+00:00
-- url     : https://prove2.me/theorems/417a513f-c732-4acd-bb8a-a21091937d2b
-- title:
--   Counting partners that share an endpoint or output mask
-- statement:
--   Let $E$ and $A$ be finite sets, and assign binary words $\ell_e,r_e:A\to\{0,1\}$ to each $e\in E$. Define its equality mask by $m_e(i)=\mathbf1_{\ell_e(i)=r_e(i)}$. Fix $e\in E$ and natural numbers $\Delta,G$. Suppose at most $\Delta$ elements share $\ell_e$, at most $\Delta$ share $r_e$, and at most $G$ share $m_e$. Then
--
--   $$
--   \bigl|\{f\in E:\ell_f=\ell_e\ \text{or}\ r_f=r_e\ \text{or}\ m_f=m_e\}\bigr|
--   \le 2\Delta+G.
--   $$
--
--   The three classes may overlap, and the count includes $e$ itself when applicable.
--
--   This controls the exceptional partner pairs that require separate treatment in the hash-family second-moment estimate.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L448-L467

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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_3

theorem ThreeSum.HashFamily.badPartners_card_le : ∀ {α : Type u_1} {E : Type u_3} [inst : Fintype.{u_3} E] [DecidableEq.{u_3 + 1} E] [inst_2 : Fintype.{u_1} α]
  [DecidableEq.{u_1 + 1} α] (left right : E → α → Bool) (e : E) (Delta G : Nat)
  (hL : @LE.le.{0} Nat instLENat (@Finset.card.{u_3} E {f : E | @Eq.{u_1 + 1} (α → Bool) (left e) (left f)}) Delta)
  (hR : @LE.le.{0} Nat instLENat (@Finset.card.{u_3} E {f : E | @Eq.{u_1 + 1} (α → Bool) (right e) (right f)}) Delta)
  (hG :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{u_3} E
        {f : E |
          @Eq.{u_1 + 1} (α → Bool) (@ThreeSum.HashFamily.outputMask.{u_1, u_3} α E left right e)
            (@ThreeSum.HashFamily.outputMask.{u_1, u_3} α E left right f)})
      G),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{u_3} E (@ThreeSum.HashFamily.badPartners.{u_1, u_3} α E inst inst_2 left right e))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Delta)
      G) := by
  sorry
