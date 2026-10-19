-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_lemma_3
-- name    : TeamDiversity.WageGap.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:25.806481+00:00
-- url     : https://prove2.me/theorems/6b048e8f-4b73-4500-bdca-97b8565cea01
-- title:
--   Lemma 3, p. 16 — the minimum collusion-proof wage w_s** = c/(f_s(2) − f_s(1)) × max{1 − δ, 1/(1 + δ(x_s − 1)), δ/(1 + δ)}
-- statement:
--   Under the standing assumptions, for every $\delta \in [0,1]$ the least specialized wage $w_s \ge 0$ satisfying (IR), the piecewise (M-IC) constraint and the (No-cycling) constraint of the specialized program is
--
--   $$w_s^{**} = \frac{c}{f_s(2)-f_s(1)} \times \max\left\{1-\delta,\ \frac{1}{1+\delta(x_s-1)},\ \frac{\delta}{1+\delta}\right\},$$
--
--   where $x_s = \frac{f_s(2)-f_s(0)}{f_s(2)-f_s(1)}$.
--
--   This is the first sentence of Lemma 3: the collusion-proof wage of a specialized team is the largest of the (work, shirk) mutual-monitoring wage, the (shirk, shirk) mutual-monitoring wage and the wage forced by the (No-cycling) constraint.
--
--   **Formalization Note** The second sentence of Lemma 3 (the diverse mutual-monitoring wage is collusion-proof) is not formalized: the paper never defines collusion in general, and the diverse program of Appendix A is taken as given.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), p. 16 (PDF 17), Lemma 3 (first sentence); program 1) of Appendix A, p. 31 (PDF 32)

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Lemma 3 (first sentence), p. 16: the minimum collusion-proof wage of a specialized team. -/
theorem lemma_3 (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd) :
    ∀ δ ∈ Set.Icc (0 : ℝ) 1,
      IsLeast (FeasS c fs δ)
        (c / (fs.f2 - fs.f1) * max (max (1 - δ) (1 / (1 + δ * (xk fs - 1)))) (δ / (1 + δ))) := by sorry

end TeamDiversity.WageGap
