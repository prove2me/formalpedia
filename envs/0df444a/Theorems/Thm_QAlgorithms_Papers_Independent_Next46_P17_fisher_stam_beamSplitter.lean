-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_fisher_stam_beamSplitter
-- name    : QAlgorithms.Papers.Independent.Next46.P17.fisher_stam_beamSplitter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:29:29.012791+00:00
-- url     : https://prove2.me/theorems/4977a694-3d6a-4719-b12b-36507f2c1a29
-- title:
--   Corollary VI.4: fisher stam beamSplitter
-- statement:
--   Let $n\geq1$ and let $\rho_X,\rho_Y$ be normalized full $n$-mode states. Assume that the actual relative entropies for all quadrature displacements of the two inputs and their 50:50 beam-splitter output are locally finite and twice differentiable at zero. Let $J$ be the unaveraged sum of the $2n$ derivatives. Then
--
--   $$
--   \frac{2}{J(\mathcal E_{1/2}(\rho_X\otimes\rho_Y))}\geq\frac1{J(\rho_X)}+\frac1{J(\rho_Y)}.
--   $$
--
--   No positivity of $J$ is added as a theorem hypothesis. On this normalized finite derivative domain, its nonvanishing is a mathematical fact. This statement makes no claim about infinite Fisher information.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 12, Corollary VI.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17

noncomputable section

open Filter MeasureTheory

open scoped ENNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

/-- PDF p.12, Corollary VI.4: quantum Stam inequality on the genuine finite
Fisher domain. No positivity of J is imposed as an extra hypothesis; absence
of a normalized translation-invariant state makes total J nonzero here.
The paper does not define an infinite-Fisher extension. -/
theorem fisher_stam_beamSplitter {n : ℕ} (hn : 0 < n)
    (rhoX rhoY : State (FockIndex n))
    (hX : TotalFisherRegular rhoX.coefficients) (hY : TotalFisherRegular rhoY.coefficients)
    (hOut : TotalFisherRegular (beamSplitter (1 / 2 : ℝ)
      (productCoeff rhoX.coefficients rhoY.coefficients))) :
    1 / totalFisher rhoX.coefficients + 1 / totalFisher rhoY.coefficients ≤
    2 / totalFisher (beamSplitter (1 / 2 : ℝ)
      (productCoeff rhoX.coefficients rhoY.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
