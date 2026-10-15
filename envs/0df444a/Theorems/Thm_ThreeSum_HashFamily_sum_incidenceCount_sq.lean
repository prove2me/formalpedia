-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_sum_incidenceCount_sq
-- name    : ThreeSum.HashFamily.sum_incidenceCount_sq
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:42:02.368291+00:00
-- url     : https://prove2.me/theorems/748e0b02-33c0-46eb-a40f-b4aef9a4969f
-- title:
--   Exact second-moment expansion of incidence counts
-- statement:
--   Let $E$ and $\Omega$ be finite sets, and let $A_e\subseteq\Omega$ be an event for each $e\in E$. For $w\in\Omega$, define the incidence count $N(w)=|\{e\in E:w\in A_e\}|$. Then
--
--   $$
--   \sum_{w\in\Omega}N(w)^2
--   =\sum_{e\in E}\sum_{f\in E}|A_e\cap A_f|.
--   $$
--
--   The right side ranges over ordered pairs, including the diagonal $e=f$. Repeated events are permitted, and no independence assumption is imposed.
--
--   This identity expresses the second moment of represented-edge counts through pairwise intersection counts, which can then be evaluated or bounded using the concrete hash family.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L403-L432

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

universe u_3 u_4

theorem ThreeSum.HashFamily.sum_incidenceCount_sq : ∀ {Ω : Type u_3} {E : Type u_4} [inst : Fintype.{u_3} Ω] [inst_1 : Fintype.{u_4} E] [inst_2 : DecidableEq.{u_3 + 1} Ω]
  (events : E → Finset.{u_3} Ω),
  @Eq.{1} Nat
    (∑ w : Ω,
      @HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@ThreeSum.HashFamily.incidenceCount.{u_3, u_4} Ω E inst_1 inst_2 events w)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (∑ e : E,
      ∑ f : E,
        @Finset.card.{u_3} Ω
          (@Inter.inter.{u_3} (Finset.{u_3} Ω) (@Finset.instInter.{u_3} Ω inst_2) (events e) (events f))) := by
  sorry
