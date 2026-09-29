-- Prove2me | Theorems.Thm_Rep_exists_shortExact_coind_res
-- name    : Rep.exists_shortExact_coind_res
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/5f04e8f1-76ee-5b2e-a3d8-f6e829a918a3
-- title:
--   Dimension-shifting short exact sequence into a coinduced representation
-- statement:
--   Let $k$ be a field, $G$ a group, and $r \colon G \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a group homomorphism into the $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$. Let $S \le G$ be a subgroup of finite index such that some intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ which is finite-dimensional over $\mathbb{Q}$ has $r^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F_0))$ contained in $S$, and let $N$ be a $k$-linear representation of $G$, finite-dimensional over $k$, each of whose vectors $n$ is fixed by all $s \in G$ with $r(s)$ in the fixing subgroup of some finite-dimensional intermediate field $F$ depending on $n$. Write $I := \mathrm{Rep.coind}\ S.\mathrm{subtype}\ (\mathrm{Rep.res}\ S.\mathrm{subtype}\ N)$ for the coinduction to $G$ of the restriction of $N$ to $S$. The assertion is that there exist a representation $Q$ of $G$ over $k$ and morphisms $\varphi \colon N \to I$ and $\psi \colon I \to Q$ of representations such that $\varphi$ is injective on underlying modules, $\psi$ is surjective, and $\psi(b) = 0$ holds exactly when $b$ lies in the image of $\varphi$; moreover $Q$ and $I$ are finite-dimensional over $k$, and every vector of $I$ and every vector of $Q$ satisfies the same level condition as the vectors of $N$, namely being fixed by all $s \in G$ whose image under $r$ fixes some finite-dimensional intermediate field.
--
--   This is the dimension-shifting embedding of a representation into the coinduction of its restriction to a finite-index subgroup, here produced together with its cokernel as a short exact sequence of finite-dimensional representations all of whose vectors have a finite level. It feeds the finiteness results for continuous cohomology used in the deformation-theoretic part of the argument, being cited by [`TWNum.finiteDimensional_continuousH2S`](thm.html#TWNum.finiteDimensional_continuousH2S) and by the finite-dimensionality statements [`groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal`](thm.html#groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal) and [`groupCohomology.finiteDimensional_continuousH2_of_isOpen_of_primeLocal`](thm.html#groupCohomology.finiteDimensional_continuousH2_of_isOpen_of_primeLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_shortExact_coind_res.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem Rep.exists_shortExact_coind_res {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G) [S.FiniteIndex]
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k G) [FiniteDimensional k N]
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : G, r s ∈ F.fixingSubgroup → N.ρ s n = n) :
    ∃ (Q : Rep.{u} k G) (φ : N ⟶ Rep.coind S.subtype (Rep.res S.subtype N))
      (ψ : Rep.coind S.subtype (Rep.res S.subtype N) ⟶ Q),
      Function.Injective φ.hom ∧ Function.Surjective ψ.hom ∧
      (∀ b, ψ.hom b = 0 ↔ ∃ a : N, φ.hom a = b) ∧
      FiniteDimensional k Q ∧ FiniteDimensional k (Rep.coind S.subtype (Rep.res S.subtype N)) ∧
      (∀ m : Rep.coind S.subtype (Rep.res S.subtype N), ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
          FiniteDimensional ℚ F ∧ ∀ s : G, r s ∈ F.fixingSubgroup → (Rep.coind S.subtype (Rep.res S.subtype N)).ρ s m = m) ∧
      (∀ m : Q, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
          FiniteDimensional ℚ F ∧ ∀ s : G, r s ∈ F.fixingSubgroup → Q.ρ s m = m) := by sorry
