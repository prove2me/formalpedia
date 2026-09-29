-- Prove2me | Theorems.Thm_Submodule_exists_isPerfPair_dotProduct_of_saturated
-- name    : Submodule.exists_isPerfPair_dotProduct_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/88850b36-0709-55c0-9fae-59456e9e90ba
-- title:
--   A perfect pairing from orthogonal saturated sublattices of ℤ^ι
-- statement:
--   Let $\iota$ be a finite type, and equip $\mathbb{Z}^{\iota}$ with the dot product $v \mathbin{⬝ᵥ} w = \sum_i v_i w_i$. Let $L$ be an abelian group regarded as a $\mathbb{Z}$-module, and let $B, E$ be $\mathbb{Z}$-submodules of $\mathbb{Z}^{\iota}$ that are saturated, in the sense that for $n \neq 0$ the relation $n \cdot v \in B$ forces $v \in B$, and likewise for $E$, and mutually orthogonal: $b \mathbin{⬝ᵥ} e = 0$ for all $b \in B$, $e \in E$. Let $f, X \colon L \to \mathbb{Z}^{\iota}$ be $\mathbb{Z}$-linear maps such that $f(y) \mathbin{⬝ᵥ} e = 0$ for all $y \in L$, $e \in E$, and $X(x) \mathbin{⬝ᵥ} b = 0$ for all $x \in L$, $b \in B$; such that $f(y) \in B$ implies $y = 0$ and $X(x) \in E$ implies $x = 0$; such that every $v \in \mathbb{Z}^{\iota}$ orthogonal to all of $E$ satisfies $v - f(y) \in B$ for some $y \in L$; and such that the image of $X$ is saturated modulo $E$: if $n \neq 0$ and $n \cdot v - X(x) \in E$ for some $x$, then $v - X(x') \in E$ for some $x'$. Then there is a $\mathbb{Z}$-bilinear form $p \colon L \times L \to \mathbb{Z}$ with $p(x,y) = X(x) \mathbin{⬝ᵥ} f(y)$ for all $x, y$, and $p$ is a perfect pairing.
--
--   This is the lattice-theoretic content of Poincaré duality for a finite oriented two-dimensional cell complex and its dual complex sharing the same set $\iota$ of $1$-cells: $B$ plays the role of the coboundaries and $E$ that of the dual boundaries, so that $f$ identifies $L$ with $E^{\perp}/B$ and $X$ embeds $L$ into $B^{\perp}/E$ with saturated image, and the dot product induces the evaluation pairing. It is used to produce the perfect integral cup-product pairing in [`ModularCurve.CupPairing.exists_perfectPairing_intCast_eq_pair`](thm.html#ModularCurve.CupPairing.exists_perfectPairing_intCast_eq_pair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_exists_isPerfPair_dotProduct_of_saturated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Submodule.exists_isPerfPair_dotProduct_of_saturated {ι : Type*} [Fintype ι]
    {L : Type*} [AddCommGroup L] [Module ℤ L]
    (B E : Submodule ℤ (ι → ℤ))
    (hB : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → n • v ∈ B → v ∈ B)
    (hE : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → n • v ∈ E → v ∈ E)
    (hBE : ∀ b ∈ B, ∀ e ∈ E, b ⬝ᵥ e = 0)
    (f X : L →ₗ[ℤ] (ι → ℤ))
    (hf : ∀ y, ∀ e ∈ E, f y ⬝ᵥ e = 0) (hX : ∀ x, ∀ b ∈ B, X x ⬝ᵥ b = 0)
    (hfB : ∀ y, f y ∈ B → y = 0) (hXE : ∀ x, X x ∈ E → x = 0)
    (hZ : ∀ v : ι → ℤ, (∀ e ∈ E, v ⬝ᵥ e = 0) → ∃ y, v - f y ∈ B)
    (hsat : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → (∃ x, n • v - X x ∈ E) → ∃ x, v - X x ∈ E) :
    ∃ p : L →ₗ[ℤ] L →ₗ[ℤ] ℤ, (∀ x y, p x y = X x ⬝ᵥ f y) ∧ p.IsPerfPair := by sorry
