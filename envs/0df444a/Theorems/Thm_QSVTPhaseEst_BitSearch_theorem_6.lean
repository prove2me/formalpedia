-- Prove2me | Theorems.Thm_QSVTPhaseEst_BitSearch_theorem_6
-- name    : QSVTPhaseEst.BitSearch.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:30.867585+00:00
-- url     : https://prove2.me/theorems/91094368-2903-4462-b14d-8f267e48dd6b
-- title:
--   Theorem 6, p. 16 — if n ≥ m and the sign function is exact, the algorithm sketch ends with θ = φ
-- statement:
--   Let $0 \le \varphi < 1$ be an $m$-bit number and $n \ge m$, $n \ge 1$, so that $\varphi$ is also an $n$-bit number. If every iteration of the loop of phase estimation by QSVT measures its bit through the exact sign function, then at the end of the procedure
--   $$\theta = \varphi.$$
--
--   This is the exact case of phase estimation by QSVT: with enough iterations and an ideal sign function, the binary search through the bits of $\varphi$ recovers $\varphi$ exactly.
--
--   **Formalization Note** "$n \ge m$" is encoded as "$\varphi = k/2^n$ for some $k \in \mathbb N$". "This procedure" is the algorithm sketch of Section V A 1 (p. 27), i.e. the loop without the additional $j = 0$ iteration; $\theta$ is its value at the end of iteration $0$. The run is any bit sequence satisfying the outcome rule with $\Delta = 0$.
-- source:
--   Martyn, Rossi, Tan & Chuang, A Grand Unification of Quantum Algorithms, arXiv:2105.02859v5, p. 16, Theorem 6 (restated p. 27, Appendix B 1)

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

namespace QSVTPhaseEst.BitSearch

theorem theorem_6 (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (n : ℕ) (hn : 1 ≤ n)
    (hbits : ∃ k : ℕ, φ = (k : ℝ) / 2 ^ n) (b : ℕ → Bool) (hrun : IsLoopRun 0 φ n b) :
    thetaAfter n b 0 = φ := by sorry

end QSVTPhaseEst.BitSearch
