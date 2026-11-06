-- Prove2me | Theorems.Thm_SilverRateSC_lemma_B_4
-- name    : SilverRateSC.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:45:48.982814+00:00
-- url     : https://prove2.me/theorems/b0cbdcfe-c64e-4e8c-9d4b-d311f4fd2736
-- title:
--   Lemma B.4 — $W^{1/p}\le x^{1/p}+y^{1/p}$ when $W=x+y+B-a$, $WB=cxy$
-- statement:
--   Fix $1\le c\le2$, $a\ge8$ and $p=p(c)=\log_2(1+\sqrt{1+c})$. If $x,y\ge a$, $B>0$, and
--   $$W=x+y+B-a,\qquad WB=cxy,$$
--   then
--   $$W^{1/p}\le x^{1/p}+y^{1/p}.$$
--
--   This scalar inequality is the induction step in the bound on the minimum checkpoint cost (Lemma B.5).
--
--   Differences from the source:
--   - encoding: standing assumptions of Appendix B (p.37): 1 ≤ c ≤ 2, a ≥ 8, p = p(c); W defined by W = x + y + B − a → explicit hypotheses; W substituted by x + y + B − a; reason: standing assumptions stated once at the start of the appendix; substitution changes no instance
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma B.4, p.40; standing assumptions of Appendix B, p.37

import Mathlib
import Definitions.Def_SilverRateSC_pOf

namespace SilverRateSC

/-- **Lemma B.4.** Fix `1 ≤ c ≤ 2`, `a ≥ 8`, and `p = p(c) = log₂(1 + √(1 + c))`. If `x, y ≥ a`,
`B > 0`, and `W = x + y + B − a`, `WB = cxy`, then `W^{1/p} ≤ x^{1/p} + y^{1/p}`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma B.4, p. 40 (standing assumptions of Appendix B, p. 37).

**Formalization Note** The standing assumptions `1 ≤ c ≤ 2`, `a ≥ 8` of Appendix B are
hypotheses; `W` is eliminated through `W = x + y + B − a`, which is positive. Powers are real
`rpow` of nonnegative bases. -/
theorem lemma_B_4 (a c x y B : ℝ) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (ha : 8 ≤ a) (hx : a ≤ x)
    (hy : a ≤ y) (hB : 0 < B) (hW : (x + y + B - a) * B = c * x * y) :
    (x + y + B - a) ^ (1 / pOf c) ≤ x ^ (1 / pOf c) + y ^ (1 / pOf c) := by sorry

end SilverRateSC
