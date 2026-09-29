-- Prove2me | Theorems.Thm_Rep_exists_dualTwist_shortExact
-- name    : Rep.exists_dualTwist_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/27e9bc4b-95c7-5275-87a4-a810901623aa
-- title:
--   Twisted duals reverse a short exact sequence of representations
-- statement:
--   Let $k$ be a field, $G$ a group (both in the same universe), and $\chi \colon G \to k^{\times}$ a group homomorphism. For a representation $A$ of $G$ over $k$, write $A^{\vee}(\chi)$ for `A.dualTwist χ`: the $k$-module $\operatorname{Hom}_k(A,k)$ with $g$ acting as $\chi(g)$ times the contragredient action of $g$. Let $M'$, $M$, $M''$ be representations of $G$ over $k$ and $i \colon M' \to M$, $\pi \colon M \to M''$ morphisms of representations such that the underlying linear map of $i$ is injective, that of $\pi$ is surjective, and for every $m \in M$ one has $\pi(m) = 0$ if and only if $m = i(m')$ for some $m' \in M'$. The assertion is the existence of morphisms of representations $\pi^{\vee} \colon M''^{\vee}(\chi) \to M^{\vee}(\chi)$ and $i^{\vee} \colon M^{\vee}(\chi) \to M'^{\vee}(\chi)$ satisfying: $(\pi^{\vee} f)(m) = f(\pi(m))$ for all $f \in M''^{\vee}(\chi)$, $m \in M$; $(i^{\vee} f)(m') = f(i(m'))$ for all $f \in M^{\vee}(\chi)$, $m' \in M'$; the underlying map of $\pi^{\vee}$ is injective; that of $i^{\vee}$ is surjective; and for every $f \in M^{\vee}(\chi)$, $i^{\vee} f = 0$ if and only if $f = \pi^{\vee} f''$ for some $f'' \in M''^{\vee}(\chi)$.
--
--   This records that applying the $\chi$-twisted dual to a short exact sequence of $k$-linear $G$-representations, presented elementwise rather than through the abelian-category machinery, yields a short exact sequence in the reverse direction, with the evaluation pairings displayed explicitly. It feeds the local-duality computations for Selmer groups, being used in [`groupCohomology.bijective_theta_dualTwist_of_sylowLevel`](thm.html#groupCohomology.bijective_theta_dualTwist_of_sylowLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_dualTwist_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_Selmer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.exists_dualTwist_shortExact {k G : Type u} [Field k] [Group G] (χ : G →* kˣ)
    {M' M M'' : Rep.{u} k G} (i : M' ⟶ M) (π : M ⟶ M'')
    (hi : Function.Injective i.hom) (hπ : Function.Surjective π.hom)
    (hex : ∀ m : M, π.hom m = 0 ↔ ∃ m' : M', i.hom m' = m) :
    ∃ (πD : M''.dualTwist χ ⟶ M.dualTwist χ) (iD : M.dualTwist χ ⟶ M'.dualTwist χ),
      (∀ (f : M''.dualTwist χ) (m : M), (πD.hom f : Module.Dual k M) m = (f : Module.Dual k M'') (π.hom m)) ∧
      (∀ (f : M.dualTwist χ) (m' : M'), (iD.hom f : Module.Dual k M') m' = (f : Module.Dual k M) (i.hom m')) ∧
      Function.Injective πD.hom ∧ Function.Surjective iD.hom ∧
      (∀ f : M.dualTwist χ, iD.hom f = 0 ↔ ∃ f'' : M''.dualTwist χ, πD.hom f'' = f) := by sorry
