-- Prove2me | Theorems.Thm_PiIrrationality_mahler_1953_eq13
-- name    : PiIrrationality.mahler_1953_eq13
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T14:29:27.141559+00:00
-- url     : https://prove2.me/theorems/72df436f-cba9-434a-8223-7ef9534e21e1
-- title:
--   Mahler (1953), §4 (13): $|\pi-p/q|>10^{-8.9101n}q^{-10}$ when $p<4q$, $n\ge50$, $10^{2.9245n}>q^{10}$
-- statement:
--   This is the intermediate estimate of Mahler's 1953 paper on rational approximations to $\pi$, stated in §4 as formulas (12)–(13).
--
--   Let $p$ and $q$ be positive integers with $p<4q$, and let $n$ be an integer satisfying
--   $$
--   n\ge 50 \qquad\text{and}\qquad 10^{2.9245\,n}>q^{10}.
--   $$
--   Then
--   $$
--   \left|\pi-\frac{p}{q}\right| > 10^{-8.9101\,n}\,q^{-10}.
--   $$
--
--   Here $n$ is an auxiliary integer (the degree parameter of Mahler's auxiliary polynomials) which may be chosen freely subject to the two displayed conditions. In §5 of the paper Mahler chooses $n$ as a function of $q$ by $10^{2.9245(n-1)}\le q^{10}<10^{2.9245n}$, which turns this estimate into the bound $|\pi-p/q|>q^{-42}$ for all sufficiently large $q$; it is therefore the analytic core of the irrationality-measure bound $\mu(\pi)\le 42$.
--
--   **Formalization Note** $p$, $q$, $n$ are natural numbers with $0<p$, $0<q$, $p<4q$, $50\le n$. The powers $10^{2.9245n}$ and $10^{-8.9101n}$ are real powers, $q^{-10}$ is written as division by $q^{10}$, and $\pi$ is Mathlib's `Real.pi`.
-- source:
--   K. Mahler, On the approximation of π, Nederl. Akad. Wetensch. Proc. Ser. A 56 = Indag. Math. 15 (1953), 30–42, §4, statements (12)–(13), original p. 32 (Documenta Math. Extra Volume Mahler Selecta (2019), p. 560). Reprint: https://content.ems.press/assets/public/full-texts/books/252/chapters/online-pdf/252-chapter-4986.pdf

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem PiIrrationality.mahler_1953_eq13 (p q n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p < 4 * q) (hn : 50 ≤ n)
    (hnq : (q : ℝ) ^ 10 < (10 : ℝ) ^ ((2.9245 : ℝ) * n)) :
    (10 : ℝ) ^ (-((8.9101 : ℝ) * n)) / (q : ℝ) ^ 10 <
      |Real.pi - (p : ℝ) / (q : ℝ)| := by sorry
