-- Prove2me | Theorems.Thm_PostQual_Incumbent_fold_only
-- name    : PostQual.Incumbent.fold_only
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:46.905011+00:00
-- url     : https://prove2.me/theorems/b987ee7d-8368-4ba2-a3e6-23f4a93bb86f
-- title:
--   Proof of Theorem 2 (ii), p. ec7 (PDF 41), (EC.15) p. ec11 — if m ≤ m⋆(x0), Π^m_0 is nondecreasing in b and V^m_0(x0,p) = (1−β)^m(p−x0)
-- statement:
--   Throughout, $(\underline R,\overline R,N,\beta,K,f_e)$ satisfies the standing assumptions of §2 ($\underline R<\overline R$, $N\ge 2$, $\beta\in(0,1)$, $K>0$, $\Delta=K/\beta<\overline R-\underline R$, $f_e$ a density supported on $[\underline R,\overline R]$, positive and continuous there) and Assumption 1 ($F_e/f_e$ nondecreasing and convex on $[\underline R,\overline R]$). Write $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$ for the left end of the incumbent's feasible drop-out prices.
--
--   Let $x_0\in[\underline R,\overline R]$, $1\le m\le N$ with $m\le m^\star(x_0)$, and $p>\ell(x_0)$. Then $b\mapsto\Pi^m_0(b;x_0,p)$ is nondecreasing on $[\ell(x_0),p]$, and
--   $$V^m_0(x_0,p)=(1-\beta)^m(p-x_0).$$
--
--   When few entrants remain, the incumbent folds: dropping out at the current price is optimal.
--
--   **Formalization Note** The standing assumptions and Assumption 1 are the hypotheses `hS : P.Standing` and `hA1 : P.Assumption1`; positivity and continuity of $f_e$ on the support are an addition to the page, needed by its own formulas $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$ and $\partial\Pi/\partial b$.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), p. ec7 (PDF 41), proof of Theorem 2 (ii), case m ≤ m⋆(x0); (EC.15), p. ec11 (PDF 45)

import Mathlib
import Definitions.Def_PostQual_Incumbent_Model

namespace PostQual.Incumbent

/-- Proof of Theorem 2 (ii), p. ec7, and (EC.15), p. ec11: if `m ≤ m⋆(x0)`, then `Π^m_0(·; x0, p)` is
nondecreasing on `[max{x0, R̲+∆}, p]` and `V^m_0(x0, p) = (1−β)^m (p − x0)`. -/
theorem fold_only (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (x0 : ℝ) (hx0 : x0 ∈ Set.Icc P.Rlo P.Rhi) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ P.N)
    (hm : m ≤ P.mStar x0) (p : ℝ) (hp : P.lo x0 < p) :
    MonotoneOn (fun b => P.Pi m b x0 p) (Set.Icc (P.lo x0) p) ∧
    P.V m x0 p = (1 - P.β) ^ m * (p - x0) := by sorry

end PostQual.Incumbent
