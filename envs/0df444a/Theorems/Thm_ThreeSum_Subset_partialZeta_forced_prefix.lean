-- Prove2me | Theorems.Thm_ThreeSum_Subset_partialZeta_forced_prefix
-- name    : ThreeSum.Subset.partialZeta_forced_prefix
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:29:48.400969+00:00
-- url     : https://prove2.me/theorems/97db1a0d-8f45-410e-8708-26cbd5df3eef
-- title:
--   A partial zeta entry gives the sum over a forced prefix
-- statement:
--   Let $f$ be an integer-valued function on finite subsets of a type with decidable equality. For a processed set $P$, define
--
--   $$Z_Pf(U)=\sum_{X\subseteq U\cap P}f\bigl((U\setminus P)\cup X\bigr).$$
--
--   Let $S_0,T$ be finite sets with $S_0\cap P=\varnothing$ and $T\subseteq P$. Then
--
--   $$Z_Pf(S_0\cup T)=\sum_{X\subseteq T}f(S_0\cup X).$$
--
--   The unprocessed part $S_0$ is forced to remain present. This permits a forced-prefix query to be read from a single entry of a stored partial zeta stage.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Subset.lean#L368-L390

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

theorem ThreeSum.Subset.partialZeta_forced_prefix : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f : Finset.{u_1} α → Int) (processed s₀ t : Finset.{u_1} α)
  (hs : @Disjoint.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α) (@Finset.instOrderBot.{u_1} α) s₀ processed)
  (ht :
    @LE.le.{u_1} (Finset.{u_1} α)
      (@Preorder.toLE.{u_1} (Finset.{u_1} α)
        (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} α) (@Finset.instPartialOrder.{u_1} α)))
      t processed),
  @Eq.{1} Int
    (@ThreeSum.Subset.partialZeta.{u_1} α inst processed f
      (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) s₀ t))
    (∑ x ∈ @Finset.powerset.{u_1} α t, f (@Union.union.{u_1} (Finset.{u_1} α) (@Finset.instUnion.{u_1} α inst) s₀ x)) := by
  sorry
