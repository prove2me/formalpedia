-- Prove2me | Theorems.Thm_PipelineInterv_Welfare_claim_2_corrected
-- name    : PipelineInterv.Welfare.claim_2_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:01.455916+00:00
-- url     : https://prove2.me/theorems/c0aed753-4759-45c8-95b5-9e7d5f31c107
-- title:
--   Claim 2, p. 8 (corrected size bound) — an ℓ1 ε-net of the simplex with at most (⌈2w/ε⌉+1)^(w−1) points
-- statement:
--   Let $w\ge1$ and $\varepsilon>0$. There is a finite set $\mathcal D(\varepsilon)\subseteq\mathcal D$ of probability distributions on $[w]$ that is an $\varepsilon$-net of $\mathcal D$ in the $\ell_1$ norm (every $D\in\mathcal D$ has some $D'\in\mathcal D(\varepsilon)$ with $\|D-D'\|_1\le\varepsilon$) and has
--   $$|\mathcal D(\varepsilon)|\ \le\ \left(\left\lceil \tfrac{2w}{\varepsilon}\right\rceil+1\right)^{w-1}.$$
--
--   The net size enters the running time of Algorithm 1; for fixed width $w$ it is polynomial in $1/\varepsilon$.
--
--   **Formalization Note (corrected size bound).** The paper states the size $(1/\varepsilon)^w$. That bound is false for large $\varepsilon$: for $w=2$ and $\varepsilon=0.8$, the two vertices of $\mathcal D$ are at $\ell_1$ distance $2$, so no single point is within $0.8$ of both and any net has at least $2$ points, while $(1/0.8)^2=1.5625$. The bound stated here is the one given by the grid of step $1/\lceil 2w/\varepsilon\rceil$; it has the same polynomial dependence on $1/\varepsilon$ for fixed $w$.
-- source:
--   Arunachaleswaran, Kannan, Roth, Ziani, Pipeline Interventions, arXiv:2002.06592v2, p. 8, Claim 2 (proof in Appendix A.2, p. 26); size bound corrected

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model

namespace PipelineInterv.Welfare
open Matrix

theorem claim_2_corrected {w : ℕ} (hw : 1 ≤ w) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset (Fin w → ℝ), IsEpsNet ε S ∧
      S.card ≤ (⌈2 * (w : ℝ) / ε⌉₊ + 1) ^ (w - 1) := by sorry

end PipelineInterv.Welfare
