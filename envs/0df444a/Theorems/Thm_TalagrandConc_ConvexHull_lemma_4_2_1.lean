-- Prove2me | Theorems.Thm_TalagrandConc_ConvexHull_lemma_4_2_1
-- name    : TalagrandConc.ConvexHull.lemma_4_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:13.292988+00:00
-- url     : https://prove2.me/theorems/dc2ee383-f92b-4e68-a4f3-07830215355d
-- title:
--   Lemma 4.2.1 — $\inf_{0\le\lambda\le1} r^{-\lambda\alpha}\exp\xi(\alpha,1-\lambda)=1+\alpha-\alpha r$
-- statement:
--   Let $\alpha\ge0$ and let $\xi(\alpha,u)=\alpha(1-u)\log(1-u)-(\alpha+1-\alpha u)\log\big(\frac{1+\alpha-\alpha u}{1+\alpha}\big)$ be the function of Eq. (4.2.1). For every $r$ with $0<r<1$,
--   $$\inf_{0\le\lambda\le1} r^{-\lambda\alpha}\exp\xi(\alpha,1-\lambda)=1+\alpha-\alpha r.$$
--
--   The function $\xi(\alpha,\cdot)$ is exactly the best replacement for $(1-\lambda)^2/4$ in Lemma 4.1.3 when the right-hand side $P(A)^{-1}$ of Theorem 4.1.1 is replaced by $P(A)^{-\alpha}$; this identity is the one-coordinate step of the proof of Theorem 4.2.4.
--
--   **Formalization Note** The infimum is taken in $[0,\infty]$ (every term is a positive real). $\alpha\ge0$ is the standing assumption of Section 4.2 (p. 126).
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 126, Lemma 4.2.1, Eq. (4.2.2)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

open scoped ENNReal

/-- Talagrand (1995), p. 126, Lemma 4.2.1, Eq. (4.2.2): for `α ≥ 0` and `0 < r < 1`,
`inf_{0 ≤ λ ≤ 1} r^{−λα} exp ξ(α, 1 − λ) = 1 + α − α r`.
The infimum is taken in `ℝ≥0∞` (all terms are positive reals). -/
theorem lemma_4_2_1 (α : ℝ) (hα : 0 ≤ α) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (⨅ l ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal (r ^ (-(l * α)) * Real.exp (xi α (1 - l))))
      = ENNReal.ofReal (1 + α - α * r) := by sorry

end TalagrandConc.ConvexHull
