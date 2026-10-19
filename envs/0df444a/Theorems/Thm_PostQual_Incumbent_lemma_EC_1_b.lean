-- Prove2me | Theorems.Thm_PostQual_Incumbent_lemma_EC_1_b
-- name    : PostQual.Incumbent.lemma_EC_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:35.775134+00:00
-- url     : https://prove2.me/theorems/200eb5e8-c687-40a9-a2b6-94fcb75ad57d
-- title:
--   Lemma EC.1 (b), p. ec7 (PDF 41) — V^{m′+1}_0(x′,p) ≥ (1−β)V^{m′}_0(x′,p)
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Fix $x'\in[\underline R,\overline R]$, $m'\in\{0,\dots,N-1\}$ and $p>\ell(x')$. Then
--   $$V^{m'+1}_0(x',p)\ge(1-\beta)V^{m'}_0(x',p).$$
--
--   One more competing entrant costs the incumbent at most the factor $1-\beta$ of his value.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec7 (PDF 41), Lemma EC.1 (b)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Lemma EC.1 (b), p. ec7: `V^{m′+1}_0(x′, p) ≥ (1−β) V^{m′}_0(x′, p)`. -/
theorem lemma_EC_1_b (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x' : ℝ) (hx' : x' ∈ Set.Icc P.Rlo P.Rhi) (m' : ℕ) (hm'N : m' + 1 ≤ P.N)
    (p : ℝ) (hp : P.lo x' < p) :
    (1 - P.β) * P.V m' x' p ≤ P.V (m' + 1) x' p := by sorry

end PostQual.Incumbent
