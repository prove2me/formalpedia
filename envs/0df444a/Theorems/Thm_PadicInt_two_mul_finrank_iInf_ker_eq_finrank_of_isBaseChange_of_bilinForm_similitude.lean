-- Prove2me | Theorems.Thm_PadicInt_two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude
-- name    : PadicInt.two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/d6da6586-2125-5f40-b667-2f28ebe636a3
-- title:
--   Similitude eigenlattice is Lagrangian: half the rank
-- statement:
--   Let $p$ be a prime, $\iota$ an index type and $P$ a finite free $\mathbb{Z}_p$-module, equipped with a family of $\mathbb{Z}_p$-linear endomorphisms $s_i$ ($i \in \iota$) and scalars $a_i \in \mathbb{Z}_p$; write $W = \bigcap_{i} \ker(s_i - a_i\,\mathrm{id})$, a $\mathbb{Z}_p$-submodule of $P$. Fix $i_0 \in \iota$ such that $s_{i_0}x - x \in W$ for every $x \in P$, and such that neither $a_{i_0} - 1$ nor $a_{i_0}$ is divisible by $p$ in $\mathbb{Z}_p$. Let $V$ be a $\mathbb{Q}_p$-vector space, also a $\mathbb{Z}_p$-module compatibly, and let $j \colon P \to V$ be a $\mathbb{Z}_p$-linear map exhibiting $V$ as the base change of $P$ along $\mathbb{Z}_p \to \mathbb{Q}_p$. Let $V'$ be a finite-dimensional $\mathbb{Q}_p$-vector space, $j_V \colon V \to V'$ an injective $\mathbb{Q}_p$-linear map, and $e \colon V' \to V'$ a linear map with $e(e v) = e v$ for all $v$ and with range equal to that of $j_V$. Let $B$ be a $\mathbb{Q}_p$-bilinear form on $V'$ with $B(v,v) = 0$ for all $v$, such that $B(v,w) = 0$ for all $w$ forces $v = 0$, and with $e$ self-adjoint for $B$: $B(ex,y) = B(x,ey)$. Finally let $g \colon V' \to V'$ be linear with $g(j_V(j(x))) = j_V(j(s_{i_0}x))$ for all $x \in P$ and $B(gx,gy) = a_{i_0} B(x,y)$ for all $x,y \in V'$, the factor taken via $\mathbb{Z}_p \to \mathbb{Q}_p$. Then $2\,\mathrm{rank}_{\mathbb{Z}_p} W = \mathrm{rank}_{\mathbb{Z}_p} P$.
--
--   The statement packages the standard argument that a lattice of simultaneous eigenvectors which is moved into itself by a similitude of a non-degenerate alternating form, with similitude factor a unit congruent to neither $0$ nor $1$ modulo $p$, is Lagrangian and hence of half the rank. It is applied to the multiplicative (ordinary) part of a $p$-adic Tate module, in the computation of the rank of the ordinary corner submodule attached to a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PadicInt.two_mul_finrank_iInf_ker_eq_finrank_of_isBaseChange_of_bilinForm_similitude
    (p : ℕ) [Fact p.Prime] {ι : Type*} {P : Type*} [AddCommGroup P] [Module ℤ_[p] P]
    [Module.Free ℤ_[p] P] [Module.Finite ℤ_[p] P]
    (s : ι → P →ₗ[ℤ_[p]] P) (a : ι → ℤ_[p]) (i₀ : ι)
    (hW₀ : ∀ x : P, s i₀ x - x ∈ ⨅ j, LinearMap.ker (s j - a j • LinearMap.id))
    (hi₀ : ¬ (p : ℤ_[p]) ∣ a i₀ - 1) (hu₀ : ¬ (p : ℤ_[p]) ∣ a i₀)
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
    (j : P →ₗ[ℤ_[p]] V) (hj : IsBaseChange ℚ_[p] j)
    {V' : Type*} [AddCommGroup V'] [Module ℚ_[p] V'] [FiniteDimensional ℚ_[p] V']
    (jV : V →ₗ[ℚ_[p]] V') (hjV : Function.Injective jV)
    (e : V' →ₗ[ℚ_[p]] V') (he : ∀ v : V', e (e v) = e v) (hrange : LinearMap.range jV = LinearMap.range e)
    (B : LinearMap.BilinForm ℚ_[p] V') (halt : ∀ v : V', B v v = 0)
    (hB : ∀ v : V', (∀ w : V', B v w = 0) → v = 0)
    (hadj : ∀ x y : V', B (e x) y = B x (e y))
    (g : V' →ₗ[ℚ_[p]] V') (hg : ∀ x : P, g (jV (j x)) = jV (j (s i₀ x)))
    (hsim : ∀ x y : V', B (g x) (g y) = algebraMap ℤ_[p] ℚ_[p] (a i₀) * B x y) :
    2 * Module.finrank ℤ_[p] ↥(⨅ j, LinearMap.ker (s j - a j • LinearMap.id)) =
      Module.finrank ℤ_[p] P := by sorry
