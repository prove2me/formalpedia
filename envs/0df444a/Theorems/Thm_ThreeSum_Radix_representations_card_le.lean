-- Prove2me | Theorems.Thm_ThreeSum_Radix_representations_card_le
-- name    : ThreeSum.Radix.representations_card_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:27:41.680665+00:00
-- url     : https://prove2.me/theorems/0418dbd3-9160-4ed6-a3ec-21f237234067
-- title:
--   Local multiplicity bounds compound once per radix digit
-- statement:
--   Let $\Omega$ be a finite set, $p\in\mathbb Z$, and $\ell,r:\Omega\to\mathbb Z$. Suppose every local fiber
--   $F(a,b)=\{\omega:p\mid a-\ell(\omega),\ p\mid b-r(\omega)\}$ has at most $B\in\mathbb N$ elements. Define the recursive representation set $R_0(a,b)=\{[]\}$; at the next level, choose $\omega\in F(a,b)$ and recurse on the quotient targets $(a-\ell(\omega))/p$ and $(b-r(\omega))/p$. Then for all $j\in\mathbb N$ and $a,b\in\mathbb Z$,
--
--   $$
--   |R_j(a,b)|\le B^j.
--   $$
--
--   The definition uses total integer division, with quotient zero when $p=0$; no nonzero-radix assumption is needed for this counting statement.
--
--   The estimate bounds global representation multiplicity without adding a separate branching factor for carries.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Radix.lean#L101-L120

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Radix.representations_card_le : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] [inst_1 : DecidableEq.{u_1 + 1} Ω] (p : Int) (left right : Ω → Int) (B : Nat)
  (hcap :
    ∀ (a b : Int),
      @LE.le.{0} Nat instLENat (@Finset.card.{u_1} Ω (@ThreeSum.Radix.localFiber.{u_1} Ω inst p left right a b)) B)
  (j : Nat) (a b : Int),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{u_1} (List.{u_1} Ω) (@ThreeSum.Radix.representations.{u_1} Ω inst inst_1 p left right j a b))
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) B j) := by
  sorry
