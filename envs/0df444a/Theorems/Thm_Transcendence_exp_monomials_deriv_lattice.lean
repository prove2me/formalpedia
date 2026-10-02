-- Prove2me | Theorems.Thm_Transcendence_exp_monomials_deriv_lattice
-- name    : Transcendence.exp_monomials_deriv_lattice
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:18:16.994861+00:00
-- url     : https://prove2.me/theorems/6e37a083-ceb0-42a9-aca6-1c6af7b701b4
-- title:
--   Derivatives of an integer combination of exponential monomials at lattice points: algebraic numbers with bounded house and denominator
-- statement:
--   Let $K$ be a number field with an embedding $\varphi : K \to \mathbb{C}$, let $\iota$ be a finite set, $n = |\iota|$, $k_0 \in \iota$, and let $x_1, \dots, x_{d_1}$ and $y_j$ ($j \in \iota$) be vectors in $\mathbb{C}^\iota$; write $\langle w, z\rangle = \sum_\nu w_\nu z_\nu$. Suppose that $x_{i\nu} = \varphi(\xi_{i\nu})$ and $e^{\langle x_i, y_j\rangle} = \varphi(a_{ij})$ with $\xi_{i\nu}, a_{ij} \in K$, and that $\eta_j \in K$ satisfy $\varphi(\eta_j) = y_{jk_0}$ if $T_0 > 0$. Suppose that an integer $\delta$ makes every $\delta\xi_{i\nu}$, $\delta\eta_j$ and $\delta a_{ij}$ an algebraic integer, and that all their houses are at most $H \ge 1$, the house of an algebraic number being the largest modulus of its conjugates. Let $T_1 \ge 1$, let $X$ be real, and let
--
--   $$F(z) = \sum_{\tau, t} p_{\tau,t}\, z_{k_0}^{\tau}\, e^{\langle t_1x_1 + \dots + t_{d_1}x_{d_1},\, z\rangle} \qquad (0 \le \tau \le T_0,\ t \in \{0, \dots, T_1\}^{d_1})$$
--
--   with integers $|p_{\tau,t}| \le X$. Then at every point $\sum_j s_jy_j$ with $0 \le s_j < S_1$, the derivative of $F$ along any list of $k$ coordinate directions is $\varphi(\gamma)$ for some $\gamma \in K$ with
--
--   $$\operatorname{house}(\gamma) \le (T_0 + 1)(T_1 + 1)^{d_1}X\,\bigl((d_1 + 1)T_1H\bigr)^{k}\,(nS_1H + k)^{T_0}\,H^{d_1nT_1S_1}$$
--
--   and $\delta^{k + T_0 + d_1nT_1S_1}\gamma$ an algebraic integer.
--
--   It is the algebraic half of Liouville's estimate (4.14) in step 2 of §4.6 of Waldschmidt's book, which `Transcendence.exp_monomials_liouville_lower` completes.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: a step of the direct proof of Corollary 4.2 in §4.6 of the book (p. 137), where Lemma 4.9 (`Transcendence.exp_monomial_derivs`) is applied at the points $\sum_js_jy_j$. The book bounds the degree and the length of the polynomial of Lemma 4.9; here the house and a denominator of the value are bounded directly. The contribution of this node is the formal proof.
-- source:
--   A step of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, §4.6, step 2 (p. 137), with Lemma 4.9 (pp. 130–131). Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

open NumberField

namespace Transcendence

/-- **Derivatives of an integer combination of exponential monomials at lattice points** (Waldschmidt,
*Diophantine Approximation on Linear Algebraic Groups*, §4.6, the algebraic half of (4.14)). Let `K` be a number
field embedded in `ℂ` by `φK`, and let `ξ i ν`, `η j`, `a i j ∈ K` be the coordinates `x i ν`, the numbers `y j k₀`
(needed only when `T₀ > 0`) and the numbers `exp ⟨xᵢ, y_j⟩`, with a common denominator `δ` and a common bound
`H ≥ 1` for their houses. Let `F(z) = Σ p_{τ,t} · z_{k₀}^τ · exp ⟨t₁x₁ + ⋯ + t_{d₁}x_{d₁}, z⟩` (`0 ≤ τ ≤ T₀`,
`t ∈ {0, …, T₁}^{d₁}`, `T₁ ≥ 1`) with integers `|p_{τ,t}| ≤ X`. Then the mixed partial derivative of `F` along the
coordinate directions `L 0, …, L (k-1)` at a lattice point `Σ_j s_j y_j` (`0 ≤ s_j < S₁`) is `φK γ` for some
`γ ∈ K` with `house γ ≤ (T₀+1)(T₁+1)^{d₁} X · ((d₁+1)T₁H)^k (nS₁H + k)^{T₀} H^{d₁nT₁S₁}` (`n = |ι|`) and
`δ^{k + T₀ + d₁nT₁S₁} γ` an algebraic integer. -/
theorem exp_monomials_deriv_lattice {K : Type*} [Field K] [NumberField K] (φK : K →+* ℂ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d₁ : ℕ} (x : Fin d₁ → ι → ℂ) (y : ι → ι → ℂ)
    (k₀ : ι) (ξ : Fin d₁ → ι → K) (hξ : ∀ i ν, φK (ξ i ν) = x i ν) (η : ι → K)
    (a : Fin d₁ → ι → K) (ha : ∀ i j, φK (a i j) = Complex.exp (∑ ν, x i ν * y j ν))
    (δ : ℤ) (hδξ : ∀ i ν, IsIntegral ℤ ((δ : K) * ξ i ν))
    (hδη : ∀ j, IsIntegral ℤ ((δ : K) * η j)) (hδa : ∀ i j, IsIntegral ℤ ((δ : K) * a i j))
    {H : ℝ} (hH : 1 ≤ H) (hξH : ∀ i ν, house (ξ i ν) ≤ H) (hηH : ∀ j, house (η j) ≤ H)
    (haH : ∀ i j, house (a i j) ≤ H) {T₀ T₁ S₁ : ℕ} (hη : 0 < T₀ → ∀ j, φK (η j) = y j k₀)
    (hT₁ : 1 ≤ T₁) (p : Fin (T₀ + 1) × (Fin d₁ → Fin (T₁ + 1)) → ℤ) {X : ℝ}
    (hp : ∀ l, |(p l : ℝ)| ≤ X) (s : ι → Fin S₁) (k : ℕ) (L : Fin k → ι) :
    ∃ γ : K, iteratedFDeriv ℂ k (fun z : ι → ℂ => ∑ l, (p l : ℂ) * (z k₀ ^ (l.1 : ℕ) *
        Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν))) (∑ j, ((s j : ℕ) : ℂ) • y j)
        (fun l => Pi.single (L l) 1) = φK γ ∧
      house γ ≤ ((T₀ : ℝ) + 1) * ((T₁ : ℝ) + 1) ^ d₁ * X * ((((d₁ : ℝ) + 1) * T₁ * H) ^ k *
        ((Fintype.card ι : ℝ) * S₁ * H + k) ^ T₀ * H ^ (d₁ * Fintype.card ι * T₁ * S₁)) ∧
      IsIntegral ℤ ((δ : K) ^ (k + T₀ + d₁ * Fintype.card ι * T₁ * S₁) * γ) := by
  sorry

end Transcendence
