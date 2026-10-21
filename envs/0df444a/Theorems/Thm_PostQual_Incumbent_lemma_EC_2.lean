-- Prove2me | Theorems.Thm_PostQual_Incumbent_lemma_EC_2
-- name    : PostQual.Incumbent.lemma_EC_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:38.798162+00:00
-- url     : https://prove2.me/theorems/0fdbb106-d260-45ed-8724-15b340c7fef6
-- title:
--   Lemma EC.2, p. ec7 (PDF 41) — H^{m′}(x0), A^{m′}_1(x0) and A^{m′}_2 hold for m⋆(x0) < m′ ≤ N
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Fix $x_0\in[\underline R,\overline R]$ and $m'$ with $m^\star(x_0)<m'\le N$. Then:
--
--   1. **$\mathbb H^{m'}(x_0)$:** for every $p>\ell(x_0)$, $b\mapsto\Pi^{m'}_0(b;x_0,p)$ is (strictly) increasing on $[\ell(x_0),b^\star_{m'}(x_0)]$ and on $[p^\star_{m'}(x_0),p]$;
--   2. **$\mathbb A^{m'}_1(x_0)$:** if $m'+1\le N$, then $p^\star_{m'+1}(x_0)\ge p^\star_{m'}(x_0)$;
--   3. **$\mathbb A^{m'}_2$:** $x\mapsto p^\star_{m'}(x)$ is nonincreasing on $\{x\in[\underline R,\overline R]:m'>m^\star(x)\}$.
--
--   Together with Lemma EC.1 (d) this gives the structure of the optimal drop-out price and the monotonicity of $p^\star$ in Theorem 2.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$. The page states the lemma for $m'=m_0+1,\dots,m$ with $m_0=m^\star(x_0)<m\le N$, which is the same as $m^\star(x_0)<m'\le N$. $\mathbb A^{m'}_1$ involves $p^\star_{m'+1}$, which (8)–(9) define only for $m'+1\le N$; that bound is stated. "Increasing" is the page's strict sense (it writes "nondecreasing" for the weak one).
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec7 (PDF 41), Lemma EC.2, with H^{m′}(x0) p. ec7 and A^{m′}_1(x0), A^{m′}_2 p. ec6 (PDF 40)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Lemma EC.2, p. ec7, with `H^{m′}(x0)`, `A^{m′}_1(x0)` and `A^{m′}_2` of pp. ec6–ec7: for every
`m′` with `m⋆(x0) < m′ ≤ N`, `Π^{m′}_0(·; x0, p)` is increasing on `[max{x0, R̲+∆}, b⋆_{m′}(x0)]` and on
`[p⋆_{m′}(x0), p]`, `p⋆_{m′+1}(x0) ≥ p⋆_{m′}(x0)`, and `p⋆_{m′}` is nonincreasing where `m′ > m⋆`. -/
theorem lemma_EC_2 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x0 : ℝ) (hx0 : x0 ∈ Set.Icc P.Rlo P.Rhi) (m' : ℕ) (hm' : P.mStar x0 < m') (hm'N : m' ≤ P.N) :
    (∀ p, P.lo x0 < p →
      StrictMonoOn (fun b => P.Pi m' b x0 p) (Set.Icc (P.lo x0) (P.bStar m' x0)) ∧
      StrictMonoOn (fun b => P.Pi m' b x0 p) (Set.Icc (P.pStar m' x0) p)) ∧
    (m' + 1 ≤ P.N → P.pStar m' x0 ≤ P.pStar (m' + 1) x0) ∧
    AntitoneOn (P.pStar m') {x | x ∈ Set.Icc P.Rlo P.Rhi ∧ P.mStar x < m'} := by sorry

end PostQual.Incumbent
