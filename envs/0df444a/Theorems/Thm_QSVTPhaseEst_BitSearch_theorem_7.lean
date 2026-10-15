-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_theorem_7
-- name    : QSVTPhaseEst.BitSearch.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:01:13.115797+00:00
-- url     : https://prove2.me/theorems/d6052245-50cb-4db1-9e02-e176ec4d3d2d
-- title:
--   Theorem 7, p. 16 — if n < m (including m = ∞) and the sign function is exact, the algorithm ends with |θ − φ| ≤ 2^{−n−1}
-- statement:
--   Let $0 \le \varphi < 1$ be an $m$-bit number with $m > n \ge 1$ (including $m = \infty$). If every iteration of phase estimation by QSVT, including the additional $j = 0$ iteration, measures its bit through the exact sign function, then the output $\theta = \theta_0.\theta_1\ldots\theta_n$ satisfies
--   $$|\theta - \varphi| \le 2^{-n-1}.$$
--
--   Together with Theorem 6, this says that with an ideal sign function the procedure always returns a best $n$-bit approximation of $\varphi$, including $\theta = 1.00\ldots0$ when that is the closest one.
--
--   **Formalization Note** "$n < m$" is encoded as "$\varphi \ne k/2^n$ for every $k \in \mathbb N$". The minor modification of p. 27, the additional $j = 0$ iteration, is encoded as Appendix B 1 b (p. 29) analyses it: the general step applied to $0.\varphi_0\varphi_1\ldots = \varphi/2$ with $\theta$ halved, whose singular value is $|\cos(\pi(\varphi - \theta_0)/2)|$; its bit is the units digit of the output. Under the literal reading of Algorithm 3, line 9, the paper's example $\varphi = 0.1110101_2$, $n = 2$ would violate the bound.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, p. 16, Theorem 7 (restated p. 27); additional j = 0 iteration: p. 27 and Appendix B 1 b, p. 29

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem theorem_7 (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 1 ≤ n)
    (hm : ¬ ∃ k : ℕ, φ = (k : ℝ) / 2 ^ n) (b : ℕ → Bool) (b₀ : Bool)
    (hrun : IsRun 0 φ n b b₀) :
    |output n b b₀ - φ| ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by sorry

end QSVTPhaseEst.BitSearch
