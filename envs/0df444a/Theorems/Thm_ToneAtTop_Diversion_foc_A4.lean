-- Prove2me | Theorems.Thm_ToneAtTop_Diversion_foc_A4
-- name    : ToneAtTop.Diversion.foc_A4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:01.720862+00:00
-- url     : https://prove2.me/theorems/09faf5e0-81d0-41bd-b001-f9df3b15d282
-- title:
--   Equation (A4), p. 28 — first-order condition for $L_1$
-- statement:
--   In the standing diversion model, suppose $2\lambda\bar x-p\tau^2>0$. Write the first-region closed form as
--
--   $$
--   L_1(c)=\frac{2\lambda\bar x+(1-c)^2\bar x^2-p\tau^2}{2(1-c)\bar x}.
--   $$
--
--   For $c\in[0,1-\tau/\bar x)$, the first-order condition $L_1'(c)=0$ holds exactly when $c=1-\sqrt{2\lambda\bar x-p\tau^2}/\bar x$. This identifies the candidate displayed in (A4). The theorem concerns the algebraic $L_1$ expression; admissibility and global optimality are addressed by Proposition 1.
-- source:
--   Penno, A Theory of Assurance: Balancing Costly Formal Control with Tone at the Top, SSRN working paper 2876700 (revision of May 2019), p. 28 (PDF 30), Appendix, proof of Proposition 1, eq. (A4)

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model

namespace ToneAtTop.Diversion

/-- Equation (A4) solves the first-order condition in the first loss region. -/
theorem foc_A4 (P : Params) (hS : P.Standing)
    (hk : 0 < 2 * P.lam * P.xbar - P.p * P.tau ^ 2) :
    ∀ c ∈ Set.Ico (0 : ℝ) (1 - P.tau / P.xbar),
      HasDerivAt
        (fun u : ℝ =>
          (2 * P.lam * P.xbar + (1 - u) ^ 2 * P.xbar ^ 2 - P.p * P.tau ^ 2) /
            (2 * (1 - u) * P.xbar))
        0 c ↔
      c = 1 - Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2) / P.xbar := by sorry

end ToneAtTop.Diversion
