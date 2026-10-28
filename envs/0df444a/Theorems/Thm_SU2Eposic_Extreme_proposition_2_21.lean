-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_proposition_2_21
-- name    : SU2Eposic.Extreme.proposition_2_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:34.461303+00:00
-- url     : https://prove2.me/theorems/564c5e39-f099-4897-8da9-d8f70ab92da9
-- title:
--   Proposition 2.21 — EC(r, m) indexed by 0 ≤ l ≤ min{r, m}
-- statement:
--   Let $r,m\in\mathbb N$. The set of EPOSIC channels from $\mathrm{End}(P_r)$ to $\mathrm{End}(P_m)$ is
--   $$EC(r,m)=\{\Phi_{m,\,r+m-2l,\,m-l}:0\le l\le\min\{r,m\}\}.$$
--
--   This re-indexes $E(r,m)$ by $l=m-h$ (Lemma 2.20), the form in which the channels are matched with the projections $q_{m,r,l}$.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 19, Proposition 2.21 (with Lemma 2.20, pp. 18–19)

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Setup

namespace SU2Eposic.Extreme

/-- **Proposition 2.21, p. 19.** `EC(r, m) = {Φ_{m, r+m−2l, m−l} : 0 ≤ l ≤ min{r, m}}`. -/
theorem proposition_2_21 (r m : ℕ) :
    EC r m = {Φ | ∃ l : ℕ, l ≤ min r m ∧ Φ = eposic r m (r + m - 2 * l) (m - l)} := by sorry

end SU2Eposic.Extreme
