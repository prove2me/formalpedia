-- Prove2me | Theorems.Thm_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
-- name    : Polynomial.nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/887da074-5a4a-543e-8e56-052d3848ce5b
-- title:
--   Cyclotomic torsion dimensions classify ℚ[X]-modules killed by Xⁿ-1
-- statement:
--   Let $M$ and $N$ be additive commutative groups, each carrying a $\mathbb{Q}[X]$-module structure and a $\mathbb{Q}$-module structure compatible with it (the scalar-tower condition for $\mathbb{Q} \to \mathbb{Q}[X]$ acting on the module), and each finite-dimensional as a $\mathbb{Q}$-vector space. Let $n$ be a natural number with $0 < n$, and assume that $X^n - 1$ annihilates $M$ and annihilates $N$, i.e. $(X^n-1)\cdot x = 0$ for every $x$ in $M$, respectively in $N$ (`Module.IsTorsionBy`). Assume further that for every $d$ dividing $n$ the $\mathbb{Q}$-dimensions of the $\Phi_d$-torsion submodules agree: $\dim_{\mathbb{Q}} \{x \in M : \Phi_d \cdot x = 0\} = \dim_{\mathbb{Q}} \{x \in N : \Phi_d \cdot x = 0\}$, where $\Phi_d =$ `cyclotomic d ℚ` is the $d$-th cyclotomic polynomial over $\mathbb{Q}$. The conclusion is that the type of $\mathbb{Q}[X]$-linear isomorphisms $M \simeq N$ is nonempty; that is, $M$ and $N$ are isomorphic as $\mathbb{Q}[X]$-modules. Note that the assertion is the mere existence of an isomorphism, with no isomorphism produced as data.
--
--   This is the classification, by the $\mathbb{Q}$-dimensions of the cyclotomic torsion pieces, of finite-dimensional rational representations of a cyclic group of order $n$ presented as $\mathbb{Q}[X]$-modules killed by $X^n-1$; it replaces the use of the decomposition $\mathbb{Q}[C_n] \cong \prod_{d \mid n} \mathbb{Q}(\zeta_d)$. It is used by [`Representation.exists_linearEquiv_of_finrank_invariants_eq`](thm.html#Representation.exists_linearEquiv_of_finrank_invariants_eq) to recognise two representations as isomorphic from numerical invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum

theorem Polynomial.nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
    {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    {N : Type v} [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N] [IsScalarTower ℚ ℚ[X] N] [FiniteDimensional ℚ N]
    {n : ℕ} (hn : 0 < n) (hM : Module.IsTorsionBy ℚ[X] M ((X : ℚ[X]) ^ n - 1)) (hN : Module.IsTorsionBy ℚ[X] N ((X : ℚ[X]) ^ n - 1))
    (h : ∀ d, d ∣ n → Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) =
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ))) :
    Nonempty (M ≃ₗ[ℚ[X]] N) := by sorry
