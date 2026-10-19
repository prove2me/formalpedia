-- Prove2me | Theorems.Thm_PostQual_Incumbent_lemma_EC_1_d
-- name    : PostQual.Incumbent.lemma_EC_1_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:33.844256+00:00
-- url     : https://prove2.me/theorems/9309054c-5f31-4be8-9e7a-b39c1a70108a
-- title:
--   Lemma EC.1 (d), p. ec7 (PDF 41) — Π^{m′}_0(b⋆;x′,p) = Π^{m′}_0(p⋆;x′,p) > Π^{m′}_0(b;x′,p) for b between them
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Fix $x'\in[\underline R,\overline R]$ and $m'\in\{1,\dots,N\}$ with $m'>m^\star(x')$. Then for all $p>\ell(x')$ and all $b\in(b^\star_{m'}(x'),p^\star_{m'}(x'))$,
--   $$\Pi^{m'}_0(b^\star_{m'}(x');x',p)=\Pi^{m'}_0(p^\star_{m'}(x');x',p)>\Pi^{m'}_0(b;x',p).$$
--
--   Between the compete threshold $b^\star$ and the switching price $p^\star$, every drop-out price is strictly worse than both; $p^\star$ is where folding immediately becomes as good as competing down to $b^\star$.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$. $p^\star_{m'}(x')$ may exceed $p$; $\Pi^{m'}_0$ is then evaluated by formula (9) with a signed integral, as on the page.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec7 (PDF 41), Lemma EC.1 (d)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Lemma EC.1 (d), p. ec7: if `m′ > m⋆(x′)`, then for every `p > max{x′, R̲+∆}` and
`b ∈ (b⋆_{m′}(x′), p⋆_{m′}(x′))`, `Π^{m′}_0(b⋆; x′, p) = Π^{m′}_0(p⋆; x′, p) > Π^{m′}_0(b; x′, p)`. -/
theorem lemma_EC_1_d (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x' : ℝ) (hx' : x' ∈ Set.Icc P.Rlo P.Rhi) (m' : ℕ) (hm'1 : 1 ≤ m') (hm'N : m' ≤ P.N)
    (hm' : P.mStar x' < m') (p : ℝ) (hp : P.lo x' < p) :
    P.Pi m' (P.bStar m' x') x' p = P.Pi m' (P.pStar m' x') x' p ∧
    ∀ b ∈ Set.Ioo (P.bStar m' x') (P.pStar m' x'),
      P.Pi m' b x' p < P.Pi m' (P.bStar m' x') x' p := by sorry

end PostQual.Incumbent
