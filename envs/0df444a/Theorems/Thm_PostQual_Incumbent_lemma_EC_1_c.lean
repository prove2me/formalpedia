-- Prove2me | Theorems.Thm_PostQual_Incumbent_lemma_EC_1_c
-- name    : PostQual.Incumbent.lemma_EC_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:26.39948+00:00
-- url     : https://prove2.me/theorems/2c9133b7-0c6e-444b-bd12-c51fe3c3fe17
-- title:
--   Lemma EC.1 (c), p. ec7 (PDF 41) — (1−β)^{−m′}V^{m′}_0(x′,p) − (p−x′) is nonincreasing in x′
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Fix $m'\in\{0,\dots,N\}$ and $p>\underline R+\Delta$. Then
--   $$x'\longmapsto(1-\beta)^{-m'}V^{m'}_0(x',p)-(p-x')$$
--   is nonincreasing on $\{x'\in[\underline R,\overline R]:x'<p\}$.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$. The page's range $p\in(\max\{x',\underline R+\Delta\},\infty)$ depends on $x'$; fixing $p>\underline R+\Delta$ and restricting $x'$ to $x'<p$ is the same set of pairs $(x',p)$.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec7 (PDF 41), Lemma EC.1 (c)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Lemma EC.1 (c), p. ec7: `(1−β)^{−m′} V^{m′}_0(x′, p) − (p − x′)` is nonincreasing in `x′`
on `[R̲, R̄]` (where `x′ < p`). -/
theorem lemma_EC_1_c (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (m' : ℕ) (hm'N : m' ≤ P.N) (p : ℝ) (hp : P.Rlo + P.Δ < p) :
    AntitoneOn (fun x => ((1 - P.β) ^ m')⁻¹ * P.V m' x p - (p - x))
      (Set.Icc P.Rlo P.Rhi ∩ Set.Iio p) := by sorry

end PostQual.Incumbent
