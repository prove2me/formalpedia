-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_6_13
-- name    : QuantumXoP.Security.lemma_6_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:30.019572+00:00
-- url     : https://prove2.me/theorems/4c28ef5f-04eb-4820-b8d7-c6250e5d188f
-- title:
--   Lemma 6.13 — $|(x+y)^r-x^r|\le r|y|(|x|+|y|)^{r-1}$
-- statement:
--   For real numbers $x,y$,
--   $$|(x+y)^r-x^r|\le r\,|y|\,(|x|+|y|)^{r-1}.$$
--
--   It bounds the cross terms in the degree-6 computation (Lemma 6.14).
--
--   **Formalization Note** $r-1$ is natural-number subtraction; at $r=0$ both sides are $0$.
--
--   Differences from the source:
--   - generalization: r is the XoP parameter, r ≥ 2 (standing assumption of §6) → every natural number r; reason: the statement specializes to every r ≥ 2
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 31 (PDF p. 33), Lemma 6.13

import Mathlib

namespace QuantumXoP.Security

/-- Lemma 6.13 (p. 31): for `x, y ∈ ℝ`, `|(x + y)^r − x^r| ≤ r |y| (|x| + |y|)^{r−1}`. -/
theorem lemma_6_13 (r : ℕ) (x y : ℝ) :
    |(x + y) ^ r - x ^ r| ≤ r * |y| * (|x| + |y|) ^ (r - 1) := by sorry

end QuantumXoP.Security
