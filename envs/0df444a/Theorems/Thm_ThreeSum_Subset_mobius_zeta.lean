-- Prove2me | Theorems.Thm_ThreeSum_Subset_mobius_zeta
-- name    : ThreeSum.Subset.mobius_zeta
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:29:46.41081+00:00
-- url     : https://prove2.me/theorems/b871b78a-744e-4942-990a-3345ff23ba88
-- title:
--   Möbius inversion on finite subsets
-- statement:
--   Let $\alpha$ have decidable equality, let $f$ be an integer-valued function on finite subsets, and let $Q$ be a finite set. Define the zeta transform by $(\zeta f)(S)=\sum_{T\subseteq S}f(T)$. Then
--
--   $$\sum_{S\subseteq Q}(-1)^{|Q|-|S|}(\zeta f)(S)=f(Q).$$
--
--   Thus the signed subset transform inverts the ordinary zeta transform exactly. This identity supplies the algebraic recovery step for the subset-counting routines.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Subset.lean#L80-L94

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Subset.mobius_zeta : ∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] (f : Finset.{u_1} α → Int) (q : Finset.{u_1} α),
  @Eq.{1} Int (@ThreeSum.Subset.mobius.{u_1} α (@ThreeSum.Subset.zeta.{u_1} α f) q) (f q) := by
  sorry
