-- Prove2me | Theorems.Thm_PostQual_Incumbent_lemma_EC_1_a
-- name    : PostQual.Incumbent.lemma_EC_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:20.995265+00:00
-- url     : https://prove2.me/theorems/4838d7a3-9330-4441-b304-b6eb95952f21
-- title:
--   Lemma EC.1 (a), p. ec7 (PDF 41) — V^{m′}_0(x′,p) is nondecreasing in p
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Fix $x'\in[\underline R,\overline R]$ and $m'\in\{0,\dots,N\}$. Then $p\mapsto V^{m'}_0(x',p)$ is nondecreasing on $(\ell(x'),\infty)$.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$. The page states (a) for all $p$; at the single point $p=\ell(x')$ the value of (8) involves $G^m_e(\cdot;0)$ with $F_e(\underline R)=0$, so the open domain the proof uses is stated.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec7 (PDF 41), Lemma EC.1 (a)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Lemma EC.1 (a), p. ec7: `V^{m′}_0(x′, p)` is nondecreasing in `p`. -/
theorem lemma_EC_1_a (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x' : ℝ) (hx' : x' ∈ Set.Icc P.Rlo P.Rhi) (m' : ℕ) (hm'N : m' ≤ P.N) :
    MonotoneOn (fun p => P.V m' x' p) (Set.Ioi (P.lo x')) := by sorry

end PostQual.Incumbent
