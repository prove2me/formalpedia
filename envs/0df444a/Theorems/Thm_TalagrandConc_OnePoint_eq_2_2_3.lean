-- Prove2me | Theorems.Thm_TalagrandConc_OnePoint_eq_2_2_3
-- name    : TalagrandConc.OnePoint.eq_2_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:48.042087+00:00
-- url     : https://prove2.me/theorems/d3a289c6-1380-4bc6-bbe3-6d6feea93c6f
-- title:
--   Eq. (2.2.3) — $a(\alpha,t)=\sup_{0\le u\le1}(1+u(e^t-1))(1-u(1-e^{-t/\alpha}))^{\alpha}$
-- statement:
--   For $\alpha>0$ and $t\ge0$, the constant $a(\alpha,t)$ of Eq. (2.2.2) (with $a(\alpha,0)=1$) is the maximum over $u\in[0,1]$ of a product of two affine-power factors:
--   $$a(\alpha,t)=\sup_{0\le u\le 1}\big(1+u(e^t-1)\big)\big(1-u(1-e^{-t/\alpha})\big)^{\alpha}.$$
--
--   In the paper the right-hand side is what the proof of Proposition 2.2.1 produces (extreme functions of the one-coordinate problem take two values), and the closed form (2.2.2) is obtained from it "by calculus"; Lemma 2.2.2 is proved from this variational form.
--
--   **Formalization Note** The supremum is the real `sSup` of the image of the compact interval $[0,1]$ under a continuous function, so it is attained and no junk value occurs. The second factor lies in $[e^{-t/\alpha},1]$, so the real power is of a positive number.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 85, Eqs. (2.2.2)–(2.2.3) (proof of Proposition 2.2.1)

import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem eq_2_2_3 (α t : ℝ) (hα : 0 < α) (ht : 0 ≤ t) :
    aAlpha α t = sSup ((fun u : ℝ =>
      (1 + u * (Real.exp t - 1)) * (1 - u * (1 - Real.exp (-t / α))) ^ α) '' Set.Icc 0 1) := by sorry

end TalagrandConc.OnePoint
