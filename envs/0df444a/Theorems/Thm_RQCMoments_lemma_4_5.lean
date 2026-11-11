-- Prove2me | Theorems.Thm_RQCMoments_lemma_4_5
-- name    : RQCMoments.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:08:19.87105+00:00
-- url     : https://prove2.me/theorems/c5bf7e38-0fbc-4826-a30b-f29c368617d2
-- title:
--   Lemma 4.5 — a nonnegative polynomial of degree $2d$ is a sum of two squares
-- statement:
--   Let $p$ be a real univariate polynomial with $p(t)\ge 0$ for all $t\in\mathbb R$ and $\deg p=2d$. Then there are real polynomials $r,s$ of degree at most $d$ with
--   $$
--   p=r^2+s^2 .
--   $$
--
--   In the proof of Theorem 4.9 this reduces nonnegative polynomials of degree at most $2k$ to the squared moduli handled by Theorem 3.2.
--
--   Differences from the source: none.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.5, p.26 (PDF p.28)

import Mathlib

set_option autoImplicit false

namespace RQCMoments

/-- **Lemma 4.5** (sum of squares decomposition) (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.5, p.26, PDF p.28).
Any non-negative univariate real polynomial of degree `2d` is a sum of two squares of real
polynomials of degree at most `d`. -/
theorem lemma_4_5 (p : Polynomial ℝ) (hp : ∀ t : ℝ, 0 ≤ p.eval t) (d : ℕ)
    (hdeg : p.natDegree = 2 * d) :
    ∃ r s : Polynomial ℝ, r.natDegree ≤ d ∧ s.natDegree ≤ d ∧ p = r ^ 2 + s ^ 2 := by sorry

end RQCMoments
