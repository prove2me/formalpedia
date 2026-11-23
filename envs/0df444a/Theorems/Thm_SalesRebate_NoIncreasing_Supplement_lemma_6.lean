-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_Supplement_lemma_6
-- name    : SalesRebate.NoIncreasing.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:17:41.665211+00:00
-- url     : https://prove2.me/theorems/b935841c-1697-4611-aa67-eff04d55857f
-- title:
--   Lemma 6, p. 32 (PDF 32) — for 0 ≤ a ≤ b ≤ c ≤ d with a² + d² = b² + c², (Φ/φ)(a)·(Φ/φ)(d) ≤ (Φ/φ)(b)·(Φ/φ)(c)
-- statement:
--   Let $\Phi$ and $\phi$ be the standard normal CDF and density. Let $0\le a\le b\le c\le d$ be real numbers with $a^2+d^2=b^2+c^2$. Then
--   $$\frac{\Phi(a)}{\phi(a)}\times\frac{\Phi(d)}{\phi(d)}\ \le\ \frac{\Phi(b)}{\phi(b)}\times\frac{\Phi(c)}{\phi(c)}.$$
--
--   The inequality is a rearrangement property of the ratio $\Phi/\phi$ on the half-line; the appendix uses it in the proof of Theorem 3 to show that the optimal spread-constrained program pays no constant rebate on top of its step ($r_{\min}=0$).
--
--   **Formalization Note** $\phi>0$ everywhere, so the four divisions are genuine.
--
--   Differences from the source: none.
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 32, Lemma 6

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

namespace SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem lemma_6 (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hsq : a ^ 2 + d ^ 2 = b ^ 2 + c ^ 2) :
    stdNormalCDF a / stdNormalPDF a * (stdNormalCDF d / stdNormalPDF d) ≤
      stdNormalCDF b / stdNormalPDF b * (stdNormalCDF c / stdNormalPDF c) := by sorry

end SalesRebate.NoIncreasing.Supplement
