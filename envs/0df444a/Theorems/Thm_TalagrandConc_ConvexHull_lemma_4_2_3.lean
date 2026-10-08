-- Prove2me | Theorems.Thm_TalagrandConc_ConvexHull_lemma_4_2_3
-- name    : TalagrandConc.ConvexHull.lemma_4_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:32.729981+00:00
-- url     : https://prove2.me/theorems/3e9505b9-2c3c-4a38-bc11-be0e9c3c84fc
-- title:
--   Lemma 4.2.3 — $1+\alpha-\alpha a\le a^{-\alpha}$ and $a+(1-a)\exp\xi(\alpha,1)\le a^{-\alpha}$
-- statement:
--   For all real $\alpha>0$ and $a>0$,
--   $$1+\alpha-\alpha a\le a^{-\alpha}\qquad\text{(4.2.3)}$$
--   and
--   $$a+(1-a)\exp\xi(\alpha,1)\le a^{-\alpha},\qquad\text{(4.2.4)}$$
--   where $\xi(\alpha,\cdot)$ is the function of Eq. (4.2.1), so that $\xi(\alpha,1)=\log(1+\alpha)$.
--
--   Inequality (4.2.4) is the case $N=1$ of Theorem 4.2.4, and (4.2.3) closes the induction step of its proof.
--
--   **Formalization Note** $a^{-\alpha}$ is the real power `Real.rpow`, well defined for $a>0$; $\xi(\alpha,1)$ uses the convention $0\cdot\log0=0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 127, Lemma 4.2.3, Eqs. (4.2.3)–(4.2.4)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

/-- Talagrand (1995), p. 127, Lemma 4.2.3: for `α, a > 0`,
`1 + α − α a ≤ a^{−α}` (Eq. (4.2.3)) and `a + (1 − a) exp ξ(α, 1) ≤ a^{−α}` (Eq. (4.2.4)). -/
theorem lemma_4_2_3 (α a : ℝ) (hα : 0 < α) (ha : 0 < a) :
    1 + α - α * a ≤ a ^ (-α) ∧ a + (1 - a) * Real.exp (xi α 1) ≤ a ^ (-α) := by sorry

end TalagrandConc.ConvexHull
