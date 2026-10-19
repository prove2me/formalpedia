-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_whiteNoiseGapStability
-- name    : QAlgorithms.Papers.Independent.Information100.P21.whiteNoiseGapStability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:13:10.527373+00:00
-- url     : https://prove2.me/theorems/550f8887-194a-4332-b31f-e1f227e38d85
-- title:
--   IX.C — full-rank stability of the certified gap
-- statement:
--   For $0\le\epsilon\le1$, put $\rho_\epsilon=(1-\epsilon)\rho_*+\epsilon I_6/6$. It is full rank, including at zero, and at least $(\epsilon/6)I_6$ in PSD order. The certificates give
--   $$R_g(\rho_\epsilon)\le(1-\epsilon)/8,\qquad R_s(\rho_\epsilon)-R_g(\rho_\epsilon)\ge(3-163\epsilon)/360.$$
--   The gap is strict for $0\le\epsilon<3/163$. In particular, $\rho_{1/200}\succeq I_6/1200$ and its gap is at least $437/72000>0.00606$. This is an exact lower bound.
--
--   PDF pp.26–27, S149–S151: retain scaled-noise feasibility and the separate standard-robustness lower bound.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 3, IX.C — full-rank stability of the certified gap

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 3, full-rank stability of the certified gap.
Round-one coverage restoration: PDF pp.26–27, S149–S151: retain scaled-noise feasibility and the separate standard-robustness lower bound. -/
theorem whiteNoiseGapStability  :
  (∀ epsilon : ℝ, 0≤epsilon → epsilon≤1 →
    QAlgorithms.IsDensityMatrix (noisyStar epsilon) ∧ (noisyStar epsilon).PosDef ∧
    (noisyStar epsilon-(epsilon/6:ℂ) • 1).PosSemidef ∧
    ((1-epsilon : ℂ) • noiseStar).PosSemidef ∧
    QAlgorithms.Entanglement.IsSeparablePositive
      (noisyStar epsilon + (1-epsilon : ℂ) • noiseStar) ∧
    rg (noisyStar epsilon)≤(1-epsilon)/8 ∧
    (1-epsilon)*2/15 - 4*epsilon/9 ≤ rs (noisyStar epsilon) ∧
    (3-163*epsilon)/360≤rs (noisyStar epsilon)-rg (noisyStar epsilon) ∧
    (epsilon<3/163 → rg (noisyStar epsilon)<rs (noisyStar epsilon))) ∧
  (noisyStar (1/200)-(1/1200:ℂ) • 1).PosSemidef ∧
  437/72000≤rs (noisyStar (1/200))-rg (noisyStar (1/200)) ∧ (0.00606:ℝ)<437/72000 := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
