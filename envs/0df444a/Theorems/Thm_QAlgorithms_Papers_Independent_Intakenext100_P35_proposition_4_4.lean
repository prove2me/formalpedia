-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_4_4
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_4_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:21:23.977111+00:00
-- url     : https://prove2.me/theorems/719940fd-ec3f-4c7f-8b38-c2cad45eb1a1
-- title:
--   Proposition 4.4
-- statement:
--   Let $s>-1$. If $g\in\mathcal V_s$ is holomorphic, then $Q_sg\in\mathcal D_s$ and $(Q_sg)'=g$. Every $f\in\mathcal D_s$ has sectorial limits at zero and infinity and satisfies
--
--   $$f(z)=f(\infty)-\frac{2^s}{\pi}\int_0^\infty\!\alpha^s\int_{\mathbb R}\frac{f'(\alpha+i\beta)}{(\alpha-i\beta+z)^{s+1}}\,d\beta\,d\alpha.$$
--
--   There nevertheless exists a measurable $g_s\in\mathcal V_s$ for which $Q_sg_s\notin\mathcal D_s$. This separates holomorphic input from arbitrary measurable input.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 20, Proposition 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 4.4, arXiv:2202.03143v1, PDF page(s) 20. -/
theorem proposition_4_4
(s : ℝ) (hs : -1 < s) :
    (∀ g, Hol hp g → WeightedDerivativeClass s g → D s (Qs s g) ∧ EqOn (deriv (Qs s g)) g hp) ∧
    (∀ f, D s f → WeightedDerivativeClass s (deriv f) ∧ SectorialLimits f ∧
      ∀ z ∈ hp, AbsoluteDouble (qsKernel s (deriv f) z) ∧
        f z = infinityValue f + Qs s (deriv f) z) ∧
    (∃ g, WeightedDerivativeClass s g ∧ ¬ D s (Qs s g)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
