-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_lemma_11
-- name    : QSVTPhaseEst.BitSearch.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:28.668784+00:00
-- url     : https://prove2.me/theorems/cdfa184b-3b28-45e6-bb9e-b9f72b915612
-- title:
--   Lemma 11, p. 27 — for an n-bit phase and the exact sign function, θ = 0.φ_{j+1}…φ_n at the end of every iteration j
-- statement:
--   Let $0 \le \varphi < 1$ be an $n$-bit number, $\varphi = 0.\varphi_1\varphi_2\ldots\varphi_n$ with $n \ge 1$, and consider any run of the loop of phase estimation by QSVT in which every bit is measured by the exact sign function (outcome rule with $\Delta = 0$). Then at the end of every iteration $j$, $0 \le j < n$,
--   $$\theta_j = 0.\varphi_{j+1}\varphi_{j+2}\ldots\varphi_n = 0.\varphi_{[j+1:]}.$$
--
--   This is the induction behind Theorem 6: each iteration extracts one more binary digit of $\varphi$, from the least significant to the most significant.
--
--   **Formalization Note** "$\varphi$ is an $n$-bit number" is $\varphi = k/2^n$ for some $k \in \mathbb N$, and $0.\varphi_{[j+1:]}$ is the fractional part of $2^j\varphi$. The run is any bit sequence satisfying the outcome rule with $\Delta = 0$; ties are allowed either way.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, p. 27, Lemma 11 (Appendix B 1 a)

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem lemma_11 (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 1 ≤ n)
    (hbits : ∃ k : ℕ, φ = (k : ℝ) / 2 ^ n) (b : ℕ → Bool) (hrun : IsLoopRun 0 φ n b) :
    ∀ j < n, thetaAfter n b j = Int.fract ((2 : ℝ) ^ j * φ) := by sorry

end QSVTPhaseEst.BitSearch
