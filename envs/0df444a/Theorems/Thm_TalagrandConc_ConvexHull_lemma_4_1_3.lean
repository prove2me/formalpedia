-- Prove2me | Theorems.Thm_TalagrandConc_ConvexHull_lemma_4_1_3
-- name    : TalagrandConc.ConvexHull.lemma_4_1_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:21.251451+00:00
-- url     : https://prove2.me/theorems/28d5137e-eefe-471a-a77c-16a1c3118b80
-- title:
--   Lemma 4.1.3 — $\inf_{0\le\lambda\le1} r^{-\lambda}\exp\frac{(1-\lambda)^2}{4}\le 2-r$
-- statement:
--   For every real $r$ with $0\le r\le 1$,
--   $$\inf_{0\le\lambda\le1} r^{-\lambda}\exp\frac{(1-\lambda)^2}{4}\le 2-r.$$
--
--   This elementary inequality (taken by the author from Johnson–Schechtman) is the one-coordinate estimate that drives the induction on $N$ in the proof of Theorem 4.1.1, applied with $r=P(A(\omega))/P(B)$.
--
--   **Formalization Note** The infimum is computed in $[0,\infty]$, where $0^{-\lambda}=+\infty$ for $\lambda>0$ and $0^0=1$; this is the meaning of $r^{-\lambda}$ at $r=0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 124, Lemma 4.1.3, Eq. (4.1.6)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

open scoped ENNReal

/-- Talagrand (1995), p. 124, Lemma 4.1.3, Eq. (4.1.6): for `0 ≤ r ≤ 1`,
`inf_{0 ≤ λ ≤ 1} r^{−λ} exp((1 − λ)²/4) ≤ 2 − r`.
Computed in `ℝ≥0∞`, so that `0^{−λ} = +∞` for `λ > 0` and `0^0 = 1`. -/
theorem lemma_4_1_3 (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (⨅ l ∈ Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal r ^ (-l) * ENNReal.ofReal (Real.exp ((1 - l) ^ 2 / 4)))
      ≤ ENNReal.ofReal (2 - r) := by sorry

end TalagrandConc.ConvexHull
