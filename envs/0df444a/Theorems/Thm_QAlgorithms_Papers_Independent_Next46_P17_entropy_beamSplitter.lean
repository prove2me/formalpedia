-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_entropy_beamSplitter
-- name    : QAlgorithms.Papers.Independent.Next46.P17.entropy_beamSplitter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:21:21.946361+00:00
-- url     : https://prove2.me/theorems/9afd3652-1042-4a42-ab27-64da70351693
-- title:
--   Quantum entropy inequality for a beam splitter
-- statement:
--   Let $n\geq1$, $0<\lambda<1$, and let $\rho_X,\rho_Y$ be arbitrary normalized states of $n$ bosonic modes on the full Hilbert space, with no photon cutoff. Let $\mathcal E_\lambda$ mix corresponding input modes by the beam splitter with quadrature matrix $\left[\begin{smallmatrix}\sqrt\lambda&\sqrt{1-\lambda}\\\sqrt{1-\lambda}&-\sqrt\lambda\end{smallmatrix}\right]$ and discard the second output. With von Neumann entropy in nats, allowing $+\infty$,
--
--   $$
--   S(\mathcal E_\lambda(\rho_X\otimes\rho_Y))\geq\lambda S(\rho_X)+(1-\lambda)S(\rho_Y).
--   $$
--
--   This bounds entropy under physical mixing of independent quantum inputs. No energy, moment, Gaussianity, or differentiability hypothesis is imposed.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 12, Theorem VII.1, (86)

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

/-- PDF p.12, Theorem VII.1, (86): arbitrary full n-mode input states,
0<lambda<1, and natural-log entropy, retaining infinity. No energy or
smoothness restriction is imposed on this numbered final theorem. -/
theorem entropy_beamSplitter {n : ℕ} (hn : 0 < n)
    (lam : ℝ) (hlam : 0 < lam) (hlamOne : lam < 1)
    (rhoX rhoY : State (FockIndex n)) :
    ENNReal.ofReal lam * extendedEntropyNats rhoX.coefficients +
      ENNReal.ofReal (1 - lam) * extendedEntropyNats rhoY.coefficients ≤
    extendedEntropyNats (beamSplitter lam
      (productCoeff rhoX.coefficients rhoY.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
