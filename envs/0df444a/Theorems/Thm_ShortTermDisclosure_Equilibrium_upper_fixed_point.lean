-- Prove2me | Theorems.Thm_ShortTermDisclosure_Equilibrium_upper_fixed_point
-- name    : ShortTermDisclosure.Equilibrium.upper_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:04.785703+00:00
-- url     : https://prove2.me/theorems/62b5257f-e677-40ce-9309-94864047a1be
-- title:
--   Equation (15) — upper-tailed Bayes fixed point
-- statement:
--   If informed managers withhold current values in $[\underline v,v')$, where $\underline v<v'\le\bar v$, the belief after silence equals $v'$ exactly when
--
--   $$\frac{p}{1-p}(v'-\underline v)^2=2(\bar v-\underline v)\left(\frac{\bar v+\underline v}{2}-v'\right).$$
--
--   This is the Bayes fixed point for the upper-tailed disclosure region. **Formalization Note** The lower endpoint is included in the withholding set as in Proposition 1.
-- source:
--   Jia & Menon, Shareholder short-termism, corporate control and voluntary disclosure, authors' manuscript (SSRN 4029096, Minerva Access copy), p. 37 (PDF 40), proof of Propositions 1 and 3, (15)

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace ShortTermDisclosure.Equilibrium

theorem upper_fixed_point (P : Params) (hP : P.Standing)
    (vp : ℝ) (hlo : P.vlo < vp) (hhi : vp ≤ P.vhi) :
    belief P (Set.Ico P.vlo vp) = vp ↔
      P.p / (1 - P.p) * (vp - P.vlo) ^ 2 =
        2 * (P.vhi - P.vlo) * ((P.vhi + P.vlo) / 2 - vp) := by sorry

end ShortTermDisclosure.Equilibrium
