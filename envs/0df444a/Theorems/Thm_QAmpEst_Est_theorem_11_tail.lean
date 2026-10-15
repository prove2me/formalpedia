-- Prove2me | Theorems.Thm_QAmpEst_Est_theorem_11_tail
-- name    : QAmpEst.Est.theorem_11_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:06.971426+00:00
-- url     : https://prove2.me/theorems/0e3e2426-14fb-45a0-baa9-07183197f18e
-- title:
--   Theorem 11, second part, p. 17 — Prob(d(X/M, ω) ≤ k/M) ≥ 1 − 1/(2(k − 1)) for every integer k > 1
-- statement:
--   Let $M \ge 1$ and $0 \le \omega < 1$, and let $X$ be the result of measuring $F_M^{-1}|S_M(\omega)\rangle$ in the computational basis. For every integer $k > 1$,
--   $$\mathrm{Prob}\big(d(X/M,\omega) \le k/M\big) \ge 1 - \frac{1}{2(k-1)} .$$
--
--   This tail bound converts the outcome law of Theorem 11 into a confidence statement for the estimate $X/M$ of $\omega$.
--
--   **Formalization Note** $k$ is a natural number, as the paper's proof sums over integers $j \ge k$. The probability of the event is the sum of $\mathrm{Prob}(X = x)$ over the outcomes $x$ in it.
-- source:
--   arXiv:quant-ph/0005055v1, Theorem 11, p. 17

import Mathlib
import Definitions.Def_QAmpEst_Est_Fourier

open scoped Real

namespace QAmpEst.Est

/-- Theorem 11 (second part), arXiv:quant-ph/0005055v1, p. 17: for every integer `k > 1`,
`Prob(d(X/M, ω) ≤ k/M) ≥ 1 − 1/(2(k − 1))`, where `X` is the outcome of measuring
`F_M⁻¹|S_M(ω)⟩` (`0 ≤ ω < 1`) in the computational basis. -/
theorem theorem_11_tail (M : ℕ) (hM : 0 < M) (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1)
    (k : ℕ) (hk : 1 < k) :
    1 - 1 / (2 * ((k : ℝ) - 1)) ≤
      ∑ x ∈ Finset.univ.filter
          (fun x : Fin M => circDist (((x : ℕ) : ℝ) / (M : ℝ)) ω ≤ (k : ℝ) / (M : ℝ)),
        phaseProb M ω x := by sorry

end QAmpEst.Est
