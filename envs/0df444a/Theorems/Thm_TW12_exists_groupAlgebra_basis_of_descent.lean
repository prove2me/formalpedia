-- Prove2me | Theorems.Thm_TW12_exists_groupAlgebra_basis_of_descent
-- name    : TW12.exists_groupAlgebra_basis_of_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/d1974aed-7e6f-5e35-9923-ee94c635bc6f
-- title:
--   Freeness over 𝒪[Δ] from matching 𝒪-ranks
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring and $p$ a prime whose image in $\mathcal{O}$ lies in the maximal ideal. Let $\Delta$ be a finite commutative group each of whose elements has order a power of $p$, and let $M$ be a module over the group algebra $\mathcal{O}[\Delta] =$ `MonoidAlgebra 𝒪 Δ`, equipped with an $\mathcal{O}$-module structure compatible with it via the structure map (a scalar tower). Suppose given $d \in \mathbb{N}$ and a family $B$ indexed by $\mathrm{Fin}(d \cdot |\Delta|)$ such that every $x \in M$ is an $\mathcal{O}$-linear combination $\sum_i a_i B_i$, and such that for every coefficient family $a$ one has $\sum_i a_i B_i = 0$ if and only if all $a_i = 0$; that is, $M$ is free of rank $d \cdot |\Delta|$ as an $\mathcal{O}$-module with basis $B$. Suppose further given an $\mathcal{O}$-module $M_0$ and an additive map $\mathrm{lam} : M \to M_0$ commuting with the $\mathcal{O}$-action, surjective, whose kernel is exactly the submodule $\mathfrak{a} \cdot M$, where $\mathfrak{a}$ is the kernel of the counit (augmentation) algebra map $\mathcal{O}[\Delta] \to \mathcal{O}$ and $\mathfrak{a} \cdot M$ denotes the product of that ideal with the full $\mathcal{O}[\Delta]$-submodule of $M$; and suppose $M_0$ is generated over $\mathcal{O}$ by $d$ elements $b_0(0), \dots, b_0(d-1)$, no independence being assumed of them. The conclusion is that there is a family $b$ indexed by $\mathrm{Fin}\,d$ in $M$ which is an $\mathcal{O}[\Delta]$-basis of $M$: every $x \in M$ is $\sum_i c_i \cdot b_i$ for some $c : \mathrm{Fin}\,d \to \mathcal{O}[\Delta]$, and $\sum_i c_i \cdot b_i = 0$ holds if and only if all $c_i = 0$.
--
--   This is the freeness criterion used in the Taylor–Wiles argument: a module over the group algebra of a finite abelian $p$-group whose $\mathcal{O}$-rank matches $|\Delta|$ times the number of generators of its coinvariants is free over the group algebra, with the rank counting replacing any direct construction of relations. It is invoked in the construction of an $\mathcal{O}[\Delta]$-basis of the corner submodule of the relevant first cohomology group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TW12_exists_groupAlgebra_basis_of_descent.lean

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Operations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TW12.exists_groupAlgebra_basis_of_descent {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {p : ℕ} [Fact p.Prime] (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (Δ : Type) [CommGroup Δ] [Fintype Δ]
    (hΔ : ∀ g : Δ, ∃ n : ℕ, g ^ (p ^ n) = 1)
    (M : Type) [AddCommGroup M] [Module (MonoidAlgebra 𝒪 Δ) M]
    [Module 𝒪 M] [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 Δ) M]
    (d : ℕ)
    (B : Fin (d * Fintype.card Δ) → M)
    (hBspan : ∀ x : M, ∃ a : Fin (d * Fintype.card Δ) → 𝒪, x = ∑ i, a i • B i)
    (hBrel : ∀ a : Fin (d * Fintype.card Δ) → 𝒪,
      ∑ i, a i • B i = 0 ↔ ∀ i, a i = 0)
    (M₀ : Type) [AddCommGroup M₀] [Module 𝒪 M₀]
    (lam : M →+ M₀)
    (hlam_smul : ∀ (a : 𝒪) (m : M), lam (a • m) = a • lam m)
    (hlam_surj : Function.Surjective lam)
    (hlam_ker : ∀ m : M, lam m = 0 ↔ m ∈
      (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 Δ))) •
        (⊤ : Submodule (MonoidAlgebra 𝒪 Δ) M))
    (b₀ : Fin d → M₀)
    (hb₀span : ∀ x : M₀, ∃ a : Fin d → 𝒪, x = ∑ i, a i • b₀ i) :
    ∃ b : Fin d → M,
      (∀ x : M, ∃ c : Fin d → MonoidAlgebra 𝒪 Δ, x = ∑ i, c i • b i) ∧
      (∀ c : Fin d → MonoidAlgebra 𝒪 Δ, ∑ i, c i • b i = 0 ↔ ∀ i, c i = 0) := by sorry
