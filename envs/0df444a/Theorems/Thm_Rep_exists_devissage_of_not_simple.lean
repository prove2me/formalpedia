-- Prove2me | Theorems.Thm_Rep_exists_devissage_of_not_simple
-- name    : Rep.exists_devissage_of_not_simple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/6108eb3c-fb99-543e-ac41-0e839620590c
-- title:
--   Dévissage of a non-simple smooth finite representation
-- statement:
--   Let $k$ be a field, $G$ a group, $r \colon G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a group homomorphism into the $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, and $N$ a $k$-linear representation of $G$ which is finite-dimensional over $k$ and satisfies the pointwise smoothness condition: for every $n \in N$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $N.\rho(s)\,n = n$ for all $s \in G$ with $r(s)$ in the fixing subgroup of $F$. Assume $N$ is not simple, i.e. it is false that every $k$-submodule $W \subseteq N$ stable under all $N.\rho(s)$ equals $\bot$ or $\top$. Then there exist representations $A$ and $C$ of $G$ over $k$ and morphisms $\varphi \colon A \to N$, $\psi \colon N \to C$ in $\mathrm{Rep}\ k\ G$ such that $A$ and $C$ satisfy the same pointwise smoothness condition, are finite-dimensional over $k$, $\varphi$ is injective on underlying modules, $\psi$ is surjective, $\psi(b) = 0$ iff $b$ lies in the image of $\varphi$, $\operatorname{finrank} A < \operatorname{finrank} N$, $\operatorname{finrank} C < \operatorname{finrank} N$, $\operatorname{finrank} A + \operatorname{finrank} C = \operatorname{finrank} N$, and the cardinalities of the images of $A.\rho$ and of $C.\rho$ are each at most that of the image of $N.\rho$.
--
--   This is the dévissage step in the induction proving a local Euler–Poincaré type identity for smooth representations: a non-simple smooth finite representation is broken into a subrepresentation and the corresponding quotient, both strictly smaller in dimension and with no larger image, so that the lexicographic measure (cardinality of the image, dimension) decreases. It is cited by [`groupCohomology.euler_poincare_identity_of_hypotheses`](thm.html#groupCohomology.euler_poincare_identity_of_hypotheses) and by [`groupCohomology.finiteDimensional_continuous_of_forall_apply_eq_of_rank_one`](thm.html#groupCohomology.finiteDimensional_continuous_of_forall_apply_eq_of_rank_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_devissage_of_not_simple.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.exists_devissage_of_not_simple {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (N : Rep.{u} k G)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : G, r s ∈ F.fixingSubgroup → N.ρ s n = n)
    [FiniteDimensional k N]
    (h : ¬ ∀ W : Submodule k N, (∀ (s : G) (v : N), v ∈ W → N.ρ s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (A C : Rep.{u} k G) (φ : A ⟶ N) (ψ : N ⟶ C),
      (∀ n : A, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : G, r s ∈ F.fixingSubgroup → A.ρ s n = n) ∧
      (∀ n : C, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : G, r s ∈ F.fixingSubgroup → C.ρ s n = n) ∧
      FiniteDimensional k A ∧ FiniteDimensional k C ∧
      Function.Injective φ.hom ∧ Function.Surjective ψ.hom ∧ (∀ b : N, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b) ∧
      Module.finrank k A < Module.finrank k N ∧ Module.finrank k C < Module.finrank k N ∧
      Module.finrank k A + Module.finrank k C = Module.finrank k N ∧
      Nat.card (MonoidHom.mrange A.ρ) ≤ Nat.card (MonoidHom.mrange N.ρ) ∧
      Nat.card (MonoidHom.mrange C.ρ) ≤ Nat.card (MonoidHom.mrange N.ρ) := by sorry
