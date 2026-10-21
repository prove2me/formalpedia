-- Prove2me | Theorems.Thm_ShortTermDisclosure_Equilibrium_two_tailed_fixed_point
-- name    : ShortTermDisclosure.Equilibrium.two_tailed_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:17.97886+00:00
-- url     : https://prove2.me/theorems/0d10c4ad-d8d9-4310-af66-9941235f2a19
-- title:
--   Equation (18) — two-tailed Bayes fixed point
-- statement:
--   If informed managers withhold current values in $(v_1,v_2)$, where $\underline v\le v_1<v_2\le\bar v$, the belief after silence equals $v_2$ exactly when
--
--   $$\frac{p}{1-p}(v_2-v_1)^2=2(\bar v-\underline v)\left(\frac{\bar v+\underline v}{2}-v_2\right).$$
--
--   Any such fixed point satisfies $v_2<(\bar v+\underline v)/2$. This is the two-tailed Bayes equation. **Formalization Note** Its left side is strictly positive because $p>0$ and $v_1<v_2$.
-- source:
--   Jia & Menon, Shareholder short-termism, corporate control and voluntary disclosure, authors' manuscript (SSRN 4029096, Minerva Access copy), p. 38 (PDF 41), proof of Propositions 1 and 3, (17)–(18)

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace ShortTermDisclosure.Equilibrium

theorem two_tailed_fixed_point (P : Params) (hP : P.Standing)
    (v1 v2 : ℝ) (hlo : P.vlo ≤ v1) (h12 : v1 < v2) (hhi : v2 ≤ P.vhi) :
    (belief P (Set.Ioo v1 v2) = v2 ↔
      P.p / (1 - P.p) * (v2 - v1) ^ 2 =
        2 * (P.vhi - P.vlo) * ((P.vhi + P.vlo) / 2 - v2)) ∧
    (belief P (Set.Ioo v1 v2) = v2 → v2 < (P.vhi + P.vlo) / 2) := by sorry

end ShortTermDisclosure.Equilibrium
