-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P05_eprPreparation
-- name    : QAlgorithms.Papers.Independent.Intake100.P05.eprPreparation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:44:22.052986+00:00
-- url     : https://prove2.me/theorems/f5d9c359-2aca-46a8-b3db-806ffb7ce1ed
-- title:
--   Homodyne conditioning of an EPR pair realizes squeezed preparation
-- statement:
--   Let $V\ge1$ be finite, in vacuum-$I$ units, and set $c=\sqrt{V^2-1}$. Start with the normalized two-mode squeezed EPR state of local quadrature variance $V$, with positive $q_Aq_B$ correlation $c$ and negative $p_Ap_B$ correlation $-c$. Alice homodynes $q_A$ when $r=0$ and $p_A$ when $r=1$. Her outcome $x$ has the centered normal density of variance $V$, strictly positive for every real $x$. The actual normalized posterior on $B$ is
--
--   $$
--   \rho_{B\mid r,x}=\rho_{r,a_r(x)},\qquad
--    a_0(x)=\frac{cx}{V},\quad a_1(x)=-\frac{cx}{V},\qquad
--    (a_r)_*G_V=G_{V-1/V}.
--   $$
--
--   Here $\rho_{r,a}$ is the pure squeezed preparation in the preceding protocol; in the selected basis its covariance is $\operatorname{diag}(1/V,V)$. The source and posterior are positive trace-one densities. At $V=1$ the induced displacement law is Dirac. This supplies an actual preparation construction, with the momentum sign fixed by the EPR anticorrelation.
-- source:
--   Continuous-variable quantum key distribution protocols over noisy channels, arXiv:0806.3954v2, PDF p. 3, Fig.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P05

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P05

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:0806.3954v2, PDF p.3, Fig.3: actual EPR preparation followed
by either quadrature homodyne produces the squeezed preparation of p.2.
Normalization is concluded. At V=1, the induced displacement law is Dirac. -/
theorem eprPreparation (V : ℝ) (hV : 1 ≤ V) :
    Integrable (fun x : ℝ × ℝ => Complex.normSq (eprWave V x)) volume ∧
    (∫ x : ℝ × ℝ, Complex.normSq (eprWave V x)) = 1 ∧
    IsContinuousDensityKernel volume (eprKernel V) ∧
    (∀ (r : Bool) (x : ℝ),
      Integrable (fun q => Complex.normSq (measuredEprWave V r x q)) volume ∧
      0 < eprBornDensity V r x ∧
      eprBornDensity V r x = normalPDF V x ∧
      eprPosteriorKernel V r x = preparedKernel V r (eprDisplacement V r x) ∧
      IsContinuousDensityKernel volume (eprPosteriorKernel V r x)) ∧
    (∀ r : Bool, Measure.map (eprDisplacement V r) (normalLaw V) =
      normalLaw (V - 1 / V)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P05

end
