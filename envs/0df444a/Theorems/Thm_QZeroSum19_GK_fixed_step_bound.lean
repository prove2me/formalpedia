-- Prove2me | Theorems.Thm_QZeroSum19_GK_fixed_step_bound
-- name    : QZeroSum19.GK.fixed_step_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:58:31.928626+00:00
-- url     : https://prove2.me/theorems/83fd27d1-eae6-4c15-a90b-54482902a996
-- title:
--   Proof of Lemma 1, p. 5 — (ln(nm/δ) + 3tε²/16)/(tε/4) = (3/4)ε + 4ln(nm/δ)/(tε) ≤ ε for t ≥ 16ln(nm/δ)/ε²
-- statement:
--   Let $n,m\in\mathbb N$, $\delta\in\mathbb R$, $\varepsilon>0$ and let $t\ge1$ be an integer. Writing $L=\ln(nm/\delta)$,
--   $$\frac{L+3t\varepsilon^2/16}{t\varepsilon/4}=\frac34\varepsilon+\frac{4L}{t\varepsilon},$$
--   and if $t\ge 16L/\varepsilon^2$ then this quantity is at most $\varepsilon$.
--
--   With the fixed step $\eta=\varepsilon/4$ the right-hand side of (3) is exactly this quantity (since $\sum_{\tau\le t}\eta=t\varepsilon/4$ and $\sum_{\tau\le t}\eta^2=t\varepsilon^2/16$); this is the computation that fixes the constant $16$ in Lemma 1.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 5, proof of Lemma 1, fixed-error display

import Mathlib

namespace QZeroSum19.GK

/-- Proof of Lemma 1, p. 5, fixed-error display: with `η = ε/4` the right-hand side of (3) is
`(ln(nm/δ) + 3tε²/16)/(tε/4) = (3/4)ε + 4 ln(nm/δ)/(tε)`, which is at most `ε` once
`t ≥ 16 ln(nm/δ)/ε²`. -/
theorem fixed_step_bound (n m : ℕ) (δ ε : ℝ) (hε : 0 < ε) (t : ℕ) (ht : 0 < t) :
    (Real.log ((n : ℝ) * m / δ) + 3 * t * ε ^ 2 / 16) / (t * ε / 4) =
        3 / 4 * ε + 4 * Real.log ((n : ℝ) * m / δ) / (t * ε) ∧
      (16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 ≤ t →
        (Real.log ((n : ℝ) * m / δ) + 3 * t * ε ^ 2 / 16) / (t * ε / 4) ≤ ε) := by sorry

end QZeroSum19.GK
