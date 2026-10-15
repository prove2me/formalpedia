-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_lemma_12
-- name    : QSVTPhaseEst.BitSearch.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:01:05.711363+00:00
-- url     : https://prove2.me/theorems/ad9f8b2e-1393-4fe7-8715-60a9bb1e914d
-- title:
--   Lemma 12, p. 28 — for φ not an n-bit number, θ after iteration j is the (n − j)-digit rounding of 0.φ_{[j+1:]}, up to a carry, with error ≤ 2^{j−n−1}
-- statement:
--   Let $0 \le \varphi < 1$ be an $m$-bit number with $m > n \ge 1$ (including $m = \infty$), and consider any run of the loop of phase estimation by QSVT with the exact sign function. Then at the end of every iteration $j$, $0 \le j < n$:
--
--   1. $\theta_j = 0.\tilde\varphi_{j+1}\ldots\tilde\varphi_n$ is an $(n-j)$-digit binary fraction, $\theta_j = k/2^{n-j}$ with $0 \le k < 2^{n-j}$;
--   2. there is a carry bit $\tilde r_j \in \{0,1\}$ such that
--   $$\bigl|\tilde r_j.\tilde\varphi_{[j+1:]} - 0.\varphi_{[j+1:]}\bigr| \le 2^{j-n-1},$$
--   where $\tilde r_j.\tilde\varphi_{[j+1:]} = \tilde r_j + \theta_j$ and $0.\varphi_{[j+1:]}$ is the fractional part of $2^j\varphi$.
--
--   Since $\tilde r_j + \theta_j$ is a multiple of $2^{-(n-j)}$ within half a grid step of $0.\varphi_{[j+1:]}$, it is a rounding of $0.\varphi_{[j+1:]}$ to $n - j$ binary digits, as the lemma states. It is the induction behind Theorem 7.
--
--   **Formalization Note** "$m > n$" is encoded as "$\varphi \ne k/2^n$ for every $k \in \mathbb N$". The bound $2^{j-n-1}$ is written $1/2^{n-j+1}$ (with $j < n$). At a tie of the rounding either rounding is allowed, as on p. 29.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, p. 28, Lemma 12 (Appendix B 1 b); proof pp. 28–29

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem lemma_12 (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 1 ≤ n)
    (hm : ¬ ∃ k : ℕ, φ = (k : ℝ) / 2 ^ n) (b : ℕ → Bool) (hrun : IsLoopRun 0 φ n b) :
    ∀ j < n,
      (∃ k : ℕ, k < 2 ^ (n - j) ∧ thetaAfter n b j = (k : ℝ) / 2 ^ (n - j)) ∧
      ∃ r : ℕ, r ≤ 1 ∧
        |(r : ℝ) + thetaAfter n b j - Int.fract ((2 : ℝ) ^ j * φ)| ≤
          ((2 : ℝ) ^ (n - j + 1))⁻¹ := by sorry

end QSVTPhaseEst.BitSearch
