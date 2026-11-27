-- Prove2me | Theorems.Thm_PrivateContinualCounting_Kraft_hilbert_log_divergence
-- name    : PrivateContinualCounting.Kraft.hilbert_log_divergence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:43:20.256792+00:00
-- url     : https://prove2.me/theorems/8e54fa29-da47-561a-89d6-a390c1ecc734
-- title:
--   Theorem 3.1 in norm form: $E_n/(\ln n)^2\to\infty$
-- statement:
--   This is Theorem 3.1 in the norm form noted at the start of Appendix A: its proof uses only the norms of the coefficients and the coefficientwise identity.
--
--   Let $(\alpha_j)_{j\ge0}$ and $(\beta_k)_{k\ge0}$ be nonnegative real sequences such that $\sum_{k\ge0}\beta_k^2<\infty$ and, for every $m\ge0$,
--
--   $$\sum_{j=0}^{m}\alpha_j\,\beta_{m-j}\ \ge\ 1.$$
--
--   Then the prefix energies $E_n=\sum_{j<n}\alpha_j^2$ satisfy
--
--   $$\lim_{n\to\infty}\frac{E_n}{(\ln n)^2}=+\infty .$$
--
--   For LTI factors with $\sum_{j=0}^m l_jr_{m-j}=1$, Cauchy–Schwarz gives $1\le\sum_{j}\|l_j\|\|r_{m-j}\|$, so the statement applies with $\alpha_j=\|l_j\|$ and $\beta_k=\|r_k\|$. It thereby yields Theorem 3.1 for scalar, vector, complex and Hilbert-space-valued coefficients, and Lemma A.1 for fixed-period counters.
--
--   **Formalization Note** The ratio is a function of the natural number $n$; for $n\in\{0,1\}$ Lean's division by $(\ln n)^2=0$ returns $0$, which does not affect the limit.
-- source:
--   Kisung Park, Sharp Limits of Time Invariance in Private Continual Counting, STOC 2027 submission #86 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/86.pdf, p. 7 (PDF p. 9), Theorem 3.1 and its proof; p. 18 (PDF p. 20), Appendix A, first paragraph (the proof uses only the norms ‖l_j‖, ‖r_k‖ and the coefficientwise identity).

import Mathlib

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft

/-- Theorem 3.1 in the norm form of Appendix A: only the norms of the coefficients and the
coefficientwise convolution inequality are used. -/
theorem hilbert_log_divergence (α β : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (hβ2 : Summable (fun k => β k ^ 2))
    (hconv : ∀ m : ℕ, 1 ≤ ∑ j ∈ Finset.range (m + 1), α j * β (m - j)) :
    Filter.Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, α j ^ 2) / (Real.log (n : ℝ)) ^ 2)
      Filter.atTop Filter.atTop := by sorry

end PrivateContinualCounting.Kraft
