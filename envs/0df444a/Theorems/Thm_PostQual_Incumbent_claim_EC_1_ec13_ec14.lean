-- Prove2me | Theorems.Thm_PostQual_Incumbent_claim_EC_1_ec13_ec14
-- name    : PostQual.Incumbent.claim_EC_1_ec13_ec14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:35.018913+00:00
-- url     : https://prove2.me/theorems/418abb44-f09c-427e-98b1-393c4a5b3b33
-- title:
--   Claim EC.1 (EC.13)–(EC.14), p. ec10 (PDF 44) — orderings of b⋆, b⋆⋆ and p⋆ across m″ ≥ m′ and x″ ≤ x′
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Fix $x'\in[\underline R,\overline R]$ and $m'\in\{1,\dots,N\}$ with $m'>m^\star(x')$, and write $b^{\star\star}_{m'}(x')=\sup\{b\in(x',\overline R+\Delta]:H(b)-L^{m'}(b,x')<0\}$. Then:
--
--   1. **(EC.13)** for every $m''\in\{m',\dots,N\}$:
--   $$p^\star_{m''}(x')>b^{\star\star}_{m''}(x')\ge b^\star_{m'}(x')\ge b^\star_{m''}(x');$$
--   2. **(EC.14)** for every $x''\in[\underline R+\Delta,\overline R+\Delta]$ with $x''\le x'$:
--   $$p^\star_{m'}(x')>b^{\star\star}_{m'}(x')\ge b^\star_{m'}(x''),\qquad b^{\star\star}_{m'}(x'')\ge b^{\star\star}_{m'}(x').$$
--
--   These orderings are what carry the shape of the incumbent's payoff from $m'$ to more entrants and to lower costs in the induction of Lemma EC.2.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$. In $b^{\star\star}$ the variable $b$ is restricted to $b>\underline R+\Delta$, where $H$ has a nonzero denominator; this leaves the supremum unchanged when $m'>m^\star(x)$.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec10 (PDF 44), Claim EC.1, (EC.13)–(EC.14)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Claim EC.1, (EC.13)–(EC.14), p. ec10: the orderings of `b⋆`, `b⋆⋆` and `p⋆` across `m″ ≥ m′`
and across `x″ ≤ x′`, when `m′ > m⋆(x′)`. -/
theorem claim_EC_1_ec13_ec14 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x' : ℝ) (hx' : x' ∈ Set.Icc P.Rlo P.Rhi) (m' : ℕ) (hm'1 : 1 ≤ m') (hm'N : m' ≤ P.N)
    (hm' : P.mStar x' < m') :
    (∀ m'' : ℕ, m' ≤ m'' → m'' ≤ P.N →
      P.bStarStar m'' x' < P.pStar m'' x' ∧ P.bStar m' x' ≤ P.bStarStar m'' x' ∧
        P.bStar m'' x' ≤ P.bStar m' x') ∧
    (∀ x'' ∈ Set.Icc (P.Rlo + P.Δ) (P.Rhi + P.Δ), x'' ≤ x' →
      P.bStarStar m' x' < P.pStar m' x' ∧ P.bStar m' x'' ≤ P.bStarStar m' x' ∧
        P.bStarStar m' x' ≤ P.bStarStar m' x'') := by sorry

end PostQual.Incumbent
