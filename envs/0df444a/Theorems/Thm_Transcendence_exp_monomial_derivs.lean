-- Prove2me | Theorems.Thm_Transcendence_exp_monomial_derivs
-- name    : Transcendence.exp_monomial_derivs
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:14.241562+00:00
-- url     : https://prove2.me/theorems/d2ef3d38-bf65-41b0-86fd-9603c916e1a3
-- title:
--   Derivatives of an exponential monomial with algebraic data: an algebraic number of controlled house and denominator
-- statement:
--   Let $K$ be a number field with an embedding $\varphi : K \to \mathbb{C}$, let $w \in K^\iota$, $\tau \in \mathbb{N}$, $k_0 \in \iota$, and $g(z) = z_{k_0}^{\tau}\exp\bigl(\sum_\nu \varphi(w_\nu) z_\nu\bigr)$. Let $q \in \mathbb{C}^\iota$ and $v \in K$ with $\varphi(v) = q_{k_0}$ if $\tau > 0$. Suppose $1 \le A$, every $w_\nu$ has house at most $A$, $v$ has house at most $B$, and $\delta w_\nu$ and $\delta v$ are algebraic integers for an integer $\delta$. Then for every list of directions $L$ of length $k$, the mixed derivative of $g$ at $q$ along $L$ equals $\varphi(\gamma)\exp\bigl(\sum_\nu \varphi(w_\nu)q_\nu\bigr)$ for some $\gamma \in K$ with
--
--   $$\operatorname{house}(\gamma) \le A^{k}(B+k)^{\tau}, \qquad \delta^{k+\tau}\gamma \text{ an algebraic integer,}$$
--
--   where the house of an algebraic number is the largest modulus of its conjugates.
--
--   This is Lemma 4.9 of Waldschmidt's book in the form needed for the Liouville step of §4.6.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Lemma 4.9 (p. 130), in the form used in §4.6. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

open NumberField

namespace Transcendence

/-- **Derivatives of exponential monomials at algebraic points** (Waldschmidt, *Diophantine Approximation on
Linear Algebraic Groups*, Lemma 4.9, in the form used by the Liouville step of §4.6). Let `K` be a number field
embedded in `ℂ` by `φ`, let `w ∈ K^ι`, and let `g(z) = z_{k₀}^τ · exp(Σ_ν φ(w_ν) z_ν)` on `ℂ^ι`. Let `q ∈ ℂ^ι` be a
point whose coordinate `q_{k₀}` is `φ(v)` with `v ∈ K` (this is only needed when `τ > 0`). Then the mixed partial
derivative of `g` at `q` along the coordinate directions `L 0, …, L (k-1)` is `φ(γ) · exp(Σ_ν φ(w_ν) q_ν)` for
some `γ ∈ K` (explicitly, a polynomial with non-negative integer coefficients in the `w_ν` and `v`) such that
* `house γ ≤ A^k (B + k)^τ`, if `1 ≤ A`, every `house w_ν ≤ A`, and `house v ≤ B`;
* `δ^{k+τ} γ` is an algebraic integer, if `δ ∈ ℤ` makes every `δ w_ν` and `δ v` an algebraic integer. -/
theorem exp_monomial_derivs {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k₀ : ι) (τ : ℕ) (w : ι → K) (v : K) (q : ι → ℂ)
    (hv : 0 < τ → φ v = q k₀) {A B : ℝ} (hA : 1 ≤ A) (hw : ∀ ν, house (w ν) ≤ A)
    (hB : house v ≤ B) (δ : ℤ) (hδw : ∀ ν, IsIntegral ℤ ((δ : K) * w ν))
    (hδv : IsIntegral ℤ ((δ : K) * v)) (k : ℕ) (L : Fin k → ι) :
    ∃ γ : K, iteratedFDeriv ℂ k (fun z : ι → ℂ => z k₀ ^ τ * Complex.exp (∑ ν, φ (w ν) * z ν)) q
        (fun l => Pi.single (L l) 1) = φ γ * Complex.exp (∑ ν, φ (w ν) * q ν) ∧
      house γ ≤ A ^ k * (B + k) ^ τ ∧ IsIntegral ℤ ((δ : K) ^ (k + τ) * γ) := by
  sorry

end Transcendence
