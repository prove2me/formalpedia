-- Prove2me | Theorems.Thm_Transcendence_exp_monomials_ne_zero
-- name    : Transcendence.exp_monomials_ne_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:28.287508+00:00
-- url     : https://prove2.me/theorems/1841b1c4-1bc4-4659-9c82-bb3bf5723fb0
-- title:
--   A non-zero combination of the monomials z^τ e^{⟨t·x, z⟩} has a non-zero derivative at the origin
-- statement:
--   Let $x_1, \dots, x_{d_1} \in \mathbb{C}^\iota$ be linearly independent over $\mathbb{Q}$, let $k_0 \in \iota$, and let $p_{\tau,t}$ ($0 \le \tau \le T_0$, $t \in \{0, \dots, T_1\}^{d_1}$) be complex numbers, not all zero. Then the entire function
--
--   $$F(z) = \sum_{\tau, t} p_{\tau,t}\, z_{k_0}^{\tau} \exp\Bigl(\sum_\nu \bigl(\textstyle\sum_i t_i x_{i\nu}\bigr) z_\nu\Bigr)$$
--
--   has a non-zero derivative of some order at the origin; in particular $F$ is not identically zero. The frequencies $\sum_i t_i x_i$ are distinct for distinct $t$; restricted to a suitable line, $F$ becomes a one-variable exponential polynomial with distinct exponents, which is not identically zero by `FourExp.expPoly_ne_zero`.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: the non-vanishing that §4.6 of the book uses (Exercises 2.4–2.5, p. 60). The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Exercises 2.4–2.5 (p. 60), in the form used in §4.6. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **Non-vanishing of exponential polynomials in several variables** (Waldschmidt, *Diophantine Approximation on
Linear Algebraic Groups*, §4.6 step 3; cf. Exercises 2.4–2.5). Let `x₁, …, x_{d₁} ∈ ℂ^ι` be linearly independent
over `ℚ`, and let `k₀ ∈ ι`. For a non-zero family of complex coefficients `p_{τ,t}` (`0 ≤ τ ≤ T₀`,
`t ∈ {0, …, T₁}^{d₁}`), the entire function `F(z) = Σ p_{τ,t} · z_{k₀}^τ · exp(⟨t₁x₁ + ⋯ + t_{d₁}x_{d₁}, z⟩)` has a
non-zero derivative of some order at the origin. (Proof: the frequencies `Σ tᵢxᵢ` are pairwise distinct; restrict
`F` to a generic line through `0` and use the one-variable statement `FourExp.expPoly_ne_zero`.) -/
theorem exp_monomials_ne_zero {ι : Type*} [Fintype ι] {d₁ : ℕ} (x : Fin d₁ → ι → ℂ)
    (hx : LinearIndependent ℚ x) (k₀ : ι) {T₀ T₁ : ℕ}
    (p : Fin (T₀ + 1) × (Fin d₁ → Fin (T₁ + 1)) → ℂ) (hp : p ≠ 0) :
    ∃ k : ℕ, iteratedFDeriv ℂ k (fun z : ι → ℂ => ∑ l, p l * (z k₀ ^ (l.1 : ℕ) *
      Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν))) 0 ≠ 0 := by
  sorry

end Transcendence
