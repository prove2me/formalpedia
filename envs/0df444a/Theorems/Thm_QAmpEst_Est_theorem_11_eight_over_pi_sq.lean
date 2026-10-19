-- Prove2me | Theorems.Thm_QAmpEst_Est_theorem_11_eight_over_pi_sq
-- name    : QAmpEst.Est.theorem_11_eight_over_pi_sq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:56:26.586518+00:00
-- url     : https://prove2.me/theorems/99513d56-968a-40a2-a548-1b4fb2bbdc54
-- title:
--   Theorem 11, third part, pp. 17–18 — Prob(d(X/M, ω) ≤ 1/M) ≥ 8/π² for M > 2
-- statement:
--   Let $M > 2$ and $0 \le \omega < 1$, and let $X$ be the result of measuring $F_M^{-1}|S_M(\omega)\rangle$ in the computational basis. Then
--   $$\mathrm{Prob}\big(d(X/M,\omega) \le 1/M\big) \ge \frac{8}{\pi^2} .$$
--
--   This is the $k = 1$ case of the confidence bound, the one that gives amplitude estimation its constant success probability $8/\pi^2$.
-- source:
--   arXiv:quant-ph/0005055v1, Theorem 11, pp. 17–18

import Mathlib
import Definitions.Def_QAmpEst_Est_Fourier

open scoped Real

namespace QAmpEst.Est

/-- Theorem 11 (third part), arXiv:quant-ph/0005055v1, pp. 17–18: in the case `k = 1` and
`M > 2`, `Prob(d(X/M, ω) ≤ 1/M) ≥ 8/π²`, where `X` is the outcome of measuring
`F_M⁻¹|S_M(ω)⟩` (`0 ≤ ω < 1`) in the computational basis. -/
theorem theorem_11_eight_over_pi_sq (M : ℕ) (hM2 : 2 < M) (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω < 1) :
    8 / π ^ 2 ≤
      ∑ x ∈ Finset.univ.filter
          (fun x : Fin M => circDist (((x : ℕ) : ℝ) / (M : ℝ)) ω ≤ 1 / (M : ℝ)),
        phaseProb M ω x := by sorry

end QAmpEst.Est
