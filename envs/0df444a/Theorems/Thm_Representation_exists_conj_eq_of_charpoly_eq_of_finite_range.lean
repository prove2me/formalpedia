-- Prove2me | Theorems.Thm_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range
-- name    : Representation.exists_conj_eq_of_charpoly_eq_of_finite_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e895c0d4-f02b-5b23-a15d-dc6b09cb54f3
-- title:
--   Finite-image GL₂(ℂ) representations with equal characteristic polynomials are conjugate
-- statement:
--   Let $G$ be a group (with its group structure as a typeclass assumption) and let $\rho, \rho' \colon G \to \mathrm{GL}_2(\mathbb{C})$ be two monoid homomorphisms into the group of invertible $2\times 2$ complex matrices indexed by `Fin 2`. Assume that the image subgroup `MonoidHom.range ρ` is finite, and likewise that the image of $\rho'$ is finite. Assume further that for every $g \in G$ the characteristic polynomial of the underlying matrix of $\rho(g)$ equals the characteristic polynomial of the underlying matrix of $\rho'(g)$, where in each case the element of $\mathrm{GL}_2(\mathbb{C})$ is coerced to a matrix in $\mathrm{Matrix}(\mathrm{Fin}\,2, \mathrm{Fin}\,2, \mathbb{C})$ and `Matrix.charpoly` is applied. The conclusion asserts the existence of a single invertible matrix $P \in \mathrm{GL}_2(\mathbb{C})$, independent of $g$, such that $\rho'(g) = P\,\rho(g)\,P^{-1}$ for all $g \in G$, the equation being an identity in the group $\mathrm{GL}_2(\mathbb{C})$. Thus equality of characteristic polynomials pointwise upgrades to conjugacy of the two representations by a fixed matrix.
--
--   This is the two-dimensional complex case of the statement that a semisimple representation of a group with finite image is determined up to conjugacy by its characteristic polynomials — equivalently, by its character, since in dimension two trace and determinant recover the characteristic polynomial; it combines Maschke semisimplicity with the linear independence of irreducible characters (the Brauer–Nesbitt principle). It is used to prove [`GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel`](thm.html#GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel), where two Galois representations agreeing on Frobenius characteristic polynomials are identified up to conjugation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem Representation.exists_conj_eq_of_charpoly_eq_of_finite_range
    {G : Type*} [Group G] (ρ ρ' : G →* GL (Fin 2) ℂ)
    (hρ : Finite (MonoidHom.range ρ)) (hρ' : Finite (MonoidHom.range ρ'))
    (h : ∀ g : G, ((ρ g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
      ((ρ' g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ g : G, ρ' g = P * ρ g * P⁻¹ := by sorry
