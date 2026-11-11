-- Prove2me | Theorems.Thm_SchattenSketch_Main_theorem_5_3
-- name    : SchattenSketch.Main.theorem_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:56:38.724694+00:00
-- url     : https://prove2.me/theorems/d7321036-7f91-438b-bdbb-38ef4bc72a42
-- title:
--   Theorem 5.3 — polynomial approximation to $\sqrt u$ [TV24]: degree $K$, coefficients $\le 2^{3K}$, uniform error $C_{poly}/K$ on $[0,1]$
-- statement:
--   There is an absolute constant $C_{poly}$ such that for every integer $K\ge 1$ there is a polynomial $P^*_K(u)=\sum_{j=0}^K a_ju^j$ with
--   $$\max_j|a_j|\le 2^{3K},\qquad \sup_{0\le u\le 1}\bigl|P^*_K(u)-\sqrt u\bigr|\le\frac{C_{poly}}K .$$
--
--   The bounded coefficients let the decoder of §5.6 turn moment estimates with relative error $\tau$ into an estimate of $\sum_i\sqrt{\lambda_i}$, hence of the tail nuclear norm.
--
--   **Formalization Note.** The coefficients are `a : Fin (K + 1) → ℝ`, so the polynomial has degree at most $K$.
--
--   Differences from the source:
--   - encoding: a degree-K polynomial P*_K(u) = Σ_{j=0}^K a_j u^j → coefficients a : Fin (K + 1) → ℝ (a_K = 0 allowed); reason: the displayed sum; a_K = 0 can be perturbed away at the cost of a larger C_poly
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 29, Theorem 5.3, (5.26) ([TV24, Lemma 4.5])

import Mathlib

namespace SchattenSketch.Main

/-- Theorem 5.3 (polynomial approximation to the square root [TV24]; Yang, p. 29). There is an
absolute constant `C_poly` such that for every `K ≥ 1` there is a polynomial of degree at most `K`,
`P*_K(u) = ∑_{j=0}^{K} a_j u^j`, with `max_j |a_j| ≤ 2^{3K}` and
`sup_{0 ≤ u ≤ 1} |P*_K(u) - √u| ≤ C_poly / K`. -/
theorem theorem_5_3 :
    ∃ C_poly : ℝ, ∀ K : ℕ, 1 ≤ K →
      ∃ a : Fin (K + 1) → ℝ, (∀ j, |a j| ≤ (2 : ℝ) ^ (3 * K)) ∧
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          |∑ j : Fin (K + 1), a j * u ^ (j : ℕ) - Real.sqrt u| ≤ C_poly / K := by sorry

end SchattenSketch.Main
