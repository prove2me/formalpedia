-- Prove2me | Theorems.Thm_Transcendence_cartesian_schwarz
-- name    : Transcendence.cartesian_schwarz
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:17:42.607365+00:00
-- url     : https://prove2.me/theorems/ad262221-bdaa-4542-9af2-2228372ffe2c
-- title:
--   Schwarz's lemma for Cartesian products: vanishing on E₁×⋯×Eₙ makes an entire function small
-- statement:
--   Let $f$ be an entire function of $n \ge 1$ complex variables, and let $E_1, \dots, E_n$ be sets of $S_1$ points in the closed disc of radius $r > 0$. Suppose that every derivative of $f$ of total order less than $nS_0$ vanishes at every point of $E_1 \times \dots \times E_n$, and that $|f| \le M$ on the polydisc of radius $R \ge 5r$. Then on the polydisc of radius $r$
--
--   $$|f| \le n\,\Bigl(\frac{2\cdot 3^{n} r}{R}\Bigr)^{S_0S_1} M.$$
--
--   This is Proposition 4.7 of Waldschmidt's book in the form used for Baker's theorem. The book assumes vanishing of the partial derivatives with every exponent below $S_0$, which the hypothesis here implies, and has $18^n$ in place of $2\cdot 3^n$. Total order is the form the application needs: vanishing with every exponent below $S_0$ is not preserved by the linear change of variables in §4.6 of the book, while vanishing by total order is.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Proof.** One variable at a time: a one-dimensional Hermite division with explicit bounds (the book's step 2.4) and a telescoping over the coordinates, so only one-variable complex analysis is used.
--
--   **Novelty.** None for the statement (the book's Proposition 4.7, with a better constant). The contribution of this node is the formal proof.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Proposition 4.7 (pp. 122–130), in the form used in §4.6. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **Schwarz's lemma for Cartesian products** (Waldschmidt, *Diophantine Approximation on Linear Algebraic
Groups*, Prop. 4.7, in the form used for Baker's theorem). Let `f` be an entire function of `n ≥ 1` complex
variables, and let `E₁, …, Eₙ` be sets of `S₁` points in the closed disc of radius `r`. If every derivative of
`f` of total order `< n·S₀` vanishes at every point of `E₁ × ⋯ × Eₙ`, and `|f| ≤ M` on the polydisc of radius
`R ≥ 5r`, then `|f| ≤ n·(2·3ⁿ·r/R)^(S₀S₁)·M` on the polydisc of radius `r`. (The book assumes vanishing of the
partial derivatives with every exponent `< S₀`, which the hypothesis here implies, and has `18ⁿ` for `2·3ⁿ`.) -/
theorem cartesian_schwarz {n : ℕ} (hn : 0 < n) (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (E : Fin n → Finset ℂ) {S₀ S₁ : ℕ} (hE : ∀ i, (E i).card = S₁)
    {r R M : ℝ} (hr : 0 < r) (hEr : ∀ i, ∀ ζ ∈ E i, ‖ζ‖ ≤ r) (hR : 5 * r ≤ R)
    (hM : ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) R, ‖f z‖ ≤ M)
    (hvan : ∀ ξ : Fin n → ℂ, (∀ i, ξ i ∈ E i) → ∀ k < n * S₀, iteratedFDeriv ℂ k f ξ = 0) :
    ∀ z ∈ Metric.closedBall (0 : Fin n → ℂ) r,
      ‖f z‖ ≤ n * (2 * 3 ^ n * r / R) ^ (S₀ * S₁) * M := by
  sorry

end Transcendence
