-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_beamSplitter_displacement_compatibility
-- name    : QAlgorithms.Papers.Independent.Next46.P17.beamSplitter_displacement_compatibility
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:24:57.641977+00:00
-- url     : https://prove2.me/theorems/73faf818-c53e-455c-b86a-e2c156d6c03e
-- title:
--   Lemma VI.1: beamSplitter displacement compatibility
-- statement:
--   Let $n\geq1$, $0<\lambda<1$, $\theta,w_X,w_Y\in\mathbb R$, and let $R$ be one of the $2n$ quadratures. Set $w=\sqrt\lambda\,w_X+\sqrt{1-\lambda}\,w_Y$. Write $D_{Q_j}(s)=e^{isP_j}$ and $D_{P_j}(s)=e^{-isQ_j}$. For every trace-class operator $X$ on the two input registers,
--
--   $$
--   \mathcal E_\lambda\!\left((D_R(w_X\theta)\otimes D_R(w_Y\theta))X(D_R(w_X\theta)\otimes D_R(w_Y\theta))^\dagger\right)
--   =D_R(w\theta)\mathcal E_\lambda(X)D_R(w\theta)^\dagger.
--   $$
--
--   This is a full channel identity and therefore includes the stated product-state specialization. It requires no moment or smoothness hypothesis.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 11, Lemma VI.1

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

/-- PDF p.11, Lemma VI.1: identity of full trace-class channel actions,
including correlated inputs. Product-state specialization follows directly.
The weights are independent and may have either sign or vanish. -/
theorem beamSplitter_displacement_compatibility {n : ℕ} (hn : 0 < n)
    (lam theta wX wY : ℝ) (hlam : 0 < lam) (hlamOne : lam < 1)
    (R : Fin n × Fin 2)
    (X : Matrix (FockIndex n × FockIndex n) (FockIndex n × FockIndex n) ℂ)
    (hX : IsTraceClass X) :
    beamSplitter lam (conjugateCoefficient
      (productCoeff (directionCoefficient R (wX * theta))
        (directionCoefficient R (wY * theta))) X) =
    directionOrbit R (beamSplitter lam X)
      ((Real.sqrt lam * wX + Real.sqrt (1 - lam) * wY) * theta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
