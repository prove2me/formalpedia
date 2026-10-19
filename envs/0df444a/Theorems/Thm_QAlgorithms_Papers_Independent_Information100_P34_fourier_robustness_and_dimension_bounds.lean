-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P34_fourier_robustness_and_dimension_bounds
-- name    : QAlgorithms.Papers.Independent.Information100.P34.fourier_robustness_and_dimension_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:56:56.93467+00:00
-- url     : https://prove2.me/theorems/652d83fb-5df0-4da0-a492-adfa6c298163
-- title:
--   Lemma 23: dimension bounds and exact robustness of Fourier channels
-- statement:
--   Let $\mathcal E:A\to B$ be any quantum channel with positive finite input and output dimensions $d_A,d_B$. For the multiplicative generalized robustness,
--
--   $$R_{\max,\mathrm{MIO}}(\mathcal E)\le d_B,\qquad R_{\max,\mathrm{DI}}(\mathcal E)\le d_A.$$
--
--   For the positive-exponent Fourier channel $\mathcal F_d$ in any positive dimension $d$,
--
--   $$R_{\max,\mathrm{MIO}}(\mathcal F_d)=R_{\max,\mathrm{DI}}(\mathcal F_d)=d,\qquad R_{\max,\mathrm{MIO}}(\mathcal F_d)=R_{\min,\mathrm{aff(MIO)}}(\mathcal F_d).$$
--
--   Robustness is $1+\lambda$, with extended infima. The affine minimum is the paper's special definition (31), evaluated for isometric Fourier channels via (B4b). The bounds identify the dimension governing coherence dilution.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, PDF p. 38, Lemma 23

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Lemma 23, Eqs.(C122-C124), PDF pp.38-39. MIO uses output dimension;
DI uses input dimension. The affine equality is asserted only for MIO. -/
theorem fourier_robustness_and_dimension_bounds :
    (∀ (a b : ℕ), 0 < a → 0 < b → ∀ E : Superop (Fin a) (Fin b),
      IsChannel E → maxRobustness .mio E ≤ (b : ℝ≥0∞) ∧
        maxRobustness .di E ≤ (a : ℝ≥0∞)) ∧
    (∀ d : ℕ, 0 < d →
      maxRobustness .mio (fourierChannel d) = (d : ℝ≥0∞) ∧
      maxRobustness .di (fourierChannel d) = (d : ℝ≥0∞) ∧
      maxRobustness .mio (fourierChannel d) =
        isometricAffineMinRobustness .mio (fourierChannel d)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P34

end
