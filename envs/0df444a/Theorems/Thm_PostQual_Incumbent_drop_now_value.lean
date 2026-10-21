-- Prove2me | Theorems.Thm_PostQual_Incumbent_drop_now_value
-- name    : PostQual.Incumbent.drop_now_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:15.001096+00:00
-- url     : https://prove2.me/theorems/071c7798-dad0-4320-a62e-4dabf1c99817
-- title:
--   Proof of Theorem 2, p. ec5 (PDF 39) — dropping out now is worth (1−β)^m(p−x0), and V^m_0(x0,p) is at least that
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Let $x_0\in[\underline R,\overline R]$, $1\le m\le N$ and $p>\ell(x_0)$. Then
--   $$\Pi^m_0(p;x_0,p)=(1-\beta)^m(p-x_0)\qquad\text{and}\qquad V^m_0(x_0,p)\ge(1-\beta)^m(p-x_0).$$
--
--   If the incumbent drops out immediately he wins only when all $m$ remaining entrants fail screening; the bound is used in (EC.7) to compare $\partial\Pi/\partial b$ with $\zeta^m$.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$. The page states the bound for $V^{m-1}_0(x_0,b)$; here it is indexed by $m\ge1$, the case $m-1=0$ being (10) itself.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec5 (PDF 39), proof of Theorem 2, the sentence after (EC.7)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Proof of Theorem 2, p. ec5: dropping out at the current price `p` yields `(1−β)^m (p − x0)`,
and the value `V^m_0(x0, p)` is at least that. -/
theorem drop_now_value (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x0 : ℝ) (hx0 : x0 ∈ Set.Icc P.Rlo P.Rhi) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ P.N)
    (p : ℝ) (hp : P.lo x0 < p) :
    P.Pi m p x0 p = (1 - P.β) ^ m * (p - x0) ∧ (1 - P.β) ^ m * (p - x0) ≤ P.V m x0 p := by sorry

end PostQual.Incumbent
