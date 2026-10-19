-- Prove2me | Theorems.Thm_PostQual_Incumbent_claim_EC_1_ec12
-- name    : PostQual.Incumbent.claim_EC_1_ec12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:34.786441+00:00
-- url     : https://prove2.me/theorems/dc33fa47-f53c-4f1a-9b4d-50b01adbaf6c
-- title:
--   Claim EC.1 (EC.12), p. ec9 (PDF 43) — sign pattern of ζ^{m′}(·;x′,p) when m′ > m⋆(x′)
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Fix $x'\in[\underline R,\overline R]$ and $m'\in\{1,\dots,N\}$ with $m'>m^\star(x')$, let $b^{\star\star}_{m'}(x')=\sup\{b\in(x',\overline R+\Delta]:H(b)-L^{m'}(b,x')<0\}$, and let $p>\ell(x')$. Then
--   $$\zeta^{m'}(b;x',p)>0\quad\text{for }b\in[\ell(x'),b^\star_{m'}(x'))\cup(b^{\star\star}_{m'}(x'),\infty),\qquad \zeta^{m'}(b;x',p)<0\quad\text{for }b\in(b^\star_{m'}(x'),b^{\star\star}_{m'}(x')).$$
--
--   Since $\zeta^{m'}$ bounds $\partial\Pi^{m'}_0/\partial b$ from above (EC.7), this sign pattern locates where the incumbent's payoff can rise in its drop-out plan.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$. The page's $(b^{\star\star},\infty]$ is taken over the reals. In $b^{\star\star}$ the variable $b$ is restricted to $b>\underline R+\Delta$, where $H$ has a nonzero denominator; this leaves the supremum unchanged when $m'>m^\star(x)$. The page leaves $p$ free; it is quantified over $p>\ell(x')$, the domain of (EC.7).
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec9 (PDF 43), Claim EC.1, (EC.12)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Claim EC.1, (EC.12), p. ec9: the sign pattern of `ζ^{m′}(·; x′, p)` when `m′ > m⋆(x′)`. -/
theorem claim_EC_1_ec12 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x' : ℝ) (hx' : x' ∈ Set.Icc P.Rlo P.Rhi) (m' : ℕ) (hm'1 : 1 ≤ m') (hm'N : m' ≤ P.N)
    (hm' : P.mStar x' < m') (p : ℝ) (hp : P.lo x' < p) :
    (∀ b ∈ Set.Ico (P.lo x') (P.bStar m' x') ∪ Set.Ioi (P.bStarStar m' x'),
      0 < P.zeta m' b x' p) ∧
    (∀ b ∈ Set.Ioo (P.bStar m' x') (P.bStarStar m' x'), P.zeta m' b x' p < 0) := by sorry

end PostQual.Incumbent
