-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_haar_averageUncertainty
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.haar_averageUncertainty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:27:53.428322+00:00
-- url     : https://prove2.me/theorems/4f7b6377-c6b2-4235-b0bf-a6a4d0c4863c
-- title:
--   Proposition B.2: exact Haar-average uncertainty and pure-state equality
-- statement:
--   For every positive integer $d$, put
--   $$h_d=\frac{\sum_{i=2}^d1/i}{\ln2}.$$
--   Fix an orthonormal basis and measure a density state $\rho$ in its rotation by $U$, chosen with normalized Haar measure on $U(d)$. If $P_U$ is the resulting outcome distribution, then the Shannon-entropy integrand is integrable and
--   $$\int H(P_U)\,dU\ge h_d.$$
--   For every normalized pure state, equality holds. Shannon entropy is in bits, while $\ln$ is natural logarithm. At $d=1$ the empty sum and deterministic entropy are both zero. This is the exact overall average uncertainty, including its pure-state equality cases.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 21, Proposition B.2: exact Haar-average uncertainty and pure-state equality

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Proposition B.2, pp.20-21: lower bound for every density state and equality
for every normalized pure state, INCLUDING d=1. Integrability is a conclusion,
not an extra hypothesis or an unguarded Bochner-integral default. -/
theorem haar_averageUncertainty (d : ℕ) (hd : 0 < d) :
    (∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      Integrable (haarMeasurementEntropy d rho) (QAlgorithms.Schur.unitaryHaar d) ∧
      haarBound d ≤ ∫ U, haarMeasurementEntropy d rho U ∂QAlgorithms.Schur.unitaryHaar d) ∧
    (∀ psi : EuclideanSpace ℂ (Fin d), IsState psi →
      Integrable (haarMeasurementEntropy d (pureDensity psi)) (QAlgorithms.Schur.unitaryHaar d) ∧
      (∫ U, haarMeasurementEntropy d (pureDensity psi) U ∂QAlgorithms.Schur.unitaryHaar d) =
        haarBound d) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
