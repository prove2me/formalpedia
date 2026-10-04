-- Prove2me | Theorems.Thm_TitsLemma_exists_ringHom_proximal
-- name    : TitsLemma.exists_ringHom_proximal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T05:57:10.707012+00:00
-- url     : https://prove2.me/theorems/3a9b510e-b7c4-4da9-8ef9-e53162a68ae5
-- title:
--   Tits — an embedding of a finitely generated real field making a trace proximal
-- statement:
--   Let $s$ be a finite set of real numbers, $K$ the subfield of $\mathbb R$ it generates, and $t \in K$. Suppose $t \ne z + z^{-1}$ for every complex root of unity $z$. Then there are a normed field $L$, a ring homomorphism $\sigma : K \to L$ and an element $\mu \in L$ with $\|\mu\| > 1$ and $\mu + \mu^{-1} = \sigma(t)$.
--
--   In other words: an element of $\mathrm{SL}_2(K)$ with trace $t$ has, after $\sigma$, an eigenvalue $\mu$ of norm greater than $1$, so it acts proximally on the projective line over $L$. The hypothesis says that the eigenvalues of such an element (the roots of $X^2 - tX + 1$) are not roots of unity. $L$ is a type in `Type` carrying a `NormedField` instance; $K$ is `Subfield.closure (s : Set ℝ)`.
--
--   Tits states (p. 263, Lemma 4.1): "Let $k$ be a finitely generated field and let $t \in k^*$ be an element of infinite order. Then, there exists a locally compact field $k'$ endowed with an absolute value $\omega$ and a homomorphism $\sigma : k \to k'$ such that $\omega(\sigma(t)) \ne 1$." The statement here is that lemma applied to an eigenvalue $\lambda$ of an element of $\mathrm{SL}_2(K)$ with trace $t$: the hypothesis on $t$ says exactly that $\lambda$ has infinite order, and then $\mu = \sigma(\lambda)$ or $\sigma(\lambda)^{-1}$ has norm greater than $1$ and $\mu + \mu^{-1} = \sigma(t)$. It is phrased with $\sigma$ defined on $K$ itself and asks only for a normed field, not a locally compact one. The proof here distinguishes three cases: $t$ transcendental, $t$ algebraic but not an algebraic integer, and $t$ an algebraic integer.
-- source:
--   Tits, J., Free subgroups in linear groups, J. Algebra 20 (1972) 250–270, https://doi.org/10.1016/0021-8693(72)90058-0, p. 263, Lemma 4.1, applied to an eigenvalue of an element of SL(2) with trace t (the field-embedding step of the proof of the Tits alternative)

import Mathlib

namespace TitsLemma

theorem exists_ringHom_proximal (s : Finset ℝ) (t : ℝ) (hts : t ∈ Subfield.closure (s : Set ℝ))
    (hinf : ∀ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → (t : ℂ) ≠ z + z⁻¹) :
    ∃ (L : Type) (_ : NormedField L) (σ : Subfield.closure (s : Set ℝ) →+* L) (μ : L),
      1 < ‖μ‖ ∧ μ + μ⁻¹ = σ ⟨t, hts⟩ := by
  sorry

end TitsLemma
