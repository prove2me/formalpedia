-- Prove2me | Theorems.Thm_TelehealthParity_Access_lemma_3
-- name    : TelehealthParity.Access.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:09.340113+00:00
-- url     : https://prove2.me/theorems/ba87c778-3bd6-4473-975b-165da22417a5
-- title:
--   Lemma 3 — $\bar\theta$ is real valued and $\bar\theta<1$ for $q>0$
-- statement:
--   Under the standing assumptions, let $q>0$ satisfy assumption (6), $0<\kappa(q)\le 1/(1+\sqrt q)^2$. Then the discriminant in the definition (19) of $\bar\theta$ is nonnegative, so that $\bar\theta$ is real valued, and $\bar\theta<1$:
--   $$\bigl(1-\kappa(q)(1-q)\bigr)^2-4q\kappa(q)\ \ge\ 0,\qquad \bar\theta<1.$$
--
--   Hence the all-balking region $[\bar\theta,1]$ of Figure 3 is a nondegenerate interval.
--
--   **Formalization Note** "Real valued" is stated as nonnegativity of the discriminant: Lean's square root returns $0$ on negative arguments, so $\bar\theta$ is always a real number in Lean and the content of "real valued" is the sign of the discriminant.
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 15, Lemma 3; proof Appendix C, EC p. 5 (PDF 38)

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting

namespace TelehealthParity.Access

theorem lemma_3 (p : Params) (hp : p.Standing) (q : ℝ) (hq : 0 < q)
    (hκ : 0 < kappa p q) (hκ' : kappa p q ≤ 1 / (1 + Real.sqrt q) ^ 2) :
    0 ≤ (1 - kappa p q * (1 - q)) ^ 2 - 4 * q * kappa p q ∧ thetaBar p q < 1 := by sorry

end TelehealthParity.Access
