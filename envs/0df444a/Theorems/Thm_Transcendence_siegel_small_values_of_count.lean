-- Prove2me | Theorems.Thm_Transcendence_siegel_small_values_of_count
-- name    : Transcendence.siegel_small_values_of_count
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:19:03.415762+00:00
-- url     : https://prove2.me/theorems/1949ad28-451d-4549-899e-5b22a33f506c
-- title:
--   An integer combination of entire functions that is small on a polydisc, for given T, X and ℓ (Proposition 4.10 with the parameters left free)
-- statement:
--   Let $\iota$ and $\Lambda$ be finite sets, $n = |\iota|$ and $L = |\Lambda|$, and let $\varphi_\lambda$ ($\lambda \in \Lambda$) be entire functions on $\mathbb{C}^\iota$ with $|\varphi_\lambda| \le B_\lambda$ on the closed polydisc of radius $R$ about $0$ and $\sum_\lambda B_\lambda \le C$, where $C > 0$. Let $0 < r < R$, and let $T$, $X$ and $\ell \ge 1$ be integers with $\ell^{2T^n} < (X+1)^{L}$. Then there are integers $p_\lambda$, not all zero, with $|p_\lambda| \le X$, such that on the closed polydisc of radius $r$
--
--   $$\Bigl|\sum_{\lambda} p_\lambda\varphi_\lambda\Bigr| \le T^n\cdot\frac{2CX}{\ell} + \frac{XC\,(r/R)^{T}}{1 - r/R}.$$
--
--   With the parameters of `Transcendence.siegel_small_values_parameters`, it gives Proposition 4.10 (`Transcendence.siegel_small_values`).
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None: the argument of §4.5 of Waldschmidt's book (Lemmas 4.11–4.13 and the proof of Proposition 4.10, pp. 132–136) with $T$, $X$ and $\ell$ left free. Thue–Siegel's lemma over $\mathbb{C}$ (the book's Lemma 4.12) is proved inside, as in the book from Lemma 4.11 applied to real and imaginary parts, with the factor $2$ in place of $\sqrt{2}$. In Lemma 4.13 the tail is bounded by `Transcendence.taylor_tail_le`. The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, §4.5: Lemmas 4.11–4.13 and the proof of Proposition 4.10 (pp. 132–136), with the parameters left free. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **An auxiliary function with small values, for given parameters** (Waldschmidt, *Diophantine
Approximation on Linear Algebraic Groups*, Prop. 4.10 with `T`, `X` and `ℓ` free, proved with Lemmas
4.11–4.13). Let `φ_λ` (`λ ∈ Λ`, `L = |Λ|`) be entire functions on `ℂ^ι` (`n = |ι|`) with `|φ_λ| ≤ B_λ` on the
closed polydisc of radius `R` (the sup-norm ball) and `Σ_λ B_λ ≤ C`, and let `0 < r < R`. If `T`, `X` and
`ℓ ≥ 1` are integers with `ℓ^{2Tⁿ} < (X + 1)^L`, there are integers `p_λ`, not all zero, with `|p_λ| ≤ X`,
such that `|Σ_λ p_λ φ_λ| ≤ Tⁿ · 2CX/ℓ + XC (r/R)^T / (1 - r/R)` on the closed polydisc of radius `r`. -/
theorem siegel_small_values_of_count {ι Λ : Type*} [Fintype ι] [Fintype Λ]
    (φ : Λ → (ι → ℂ) → ℂ) (hφ : ∀ l, AnalyticOnNhd ℂ (φ l) Set.univ) {r R C : ℝ}
    (hr : 0 < r) (hrR : r < R) (B : Λ → ℝ)
    (hB : ∀ l, ∀ z ∈ Metric.closedBall (0 : ι → ℂ) R, ‖φ l z‖ ≤ B l)
    (hC : 0 < C) (hBC : ∑ l, B l ≤ C) {T X ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcount : ℓ ^ (2 * T ^ Fintype.card ι) < (X + 1) ^ Fintype.card Λ) :
    ∃ p : Λ → ℤ, p ≠ 0 ∧ (∀ l, |p l| ≤ X) ∧
      ∀ z ∈ Metric.closedBall (0 : ι → ℂ) r, ‖∑ l, (p l : ℂ) * φ l z‖ ≤
        (T : ℝ) ^ Fintype.card ι * (2 * (C * X / ℓ)) + X * C * (r / R) ^ T / (1 - r / R) := by
  sorry

end Transcendence
