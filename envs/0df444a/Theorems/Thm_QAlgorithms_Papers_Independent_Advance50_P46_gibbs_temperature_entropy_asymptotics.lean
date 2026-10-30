-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_gibbs_temperature_entropy_asymptotics
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.gibbs_temperature_entropy_asymptotics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:15:59.114438+00:00
-- url     : https://prove2.me/theorems/5015c255-95b3-487d-9483-7df4e904b4ef
-- title:
--   Theorem 3, inverse-temperature and entropy asymptotics
-- statement:
--   Let $H$ be an unbounded semibounded self-adjoint Hamiltonian satisfying the Gibbs hypothesis on an infinite-dimensional separable complex Hilbert space. In a complete energy eigenbasis, count each eigenvalue with its multiplicity and define $N_H^\uparrow(L)=\sum_{\lambda_j+\lambda_k\le L}\lambda_j^2$ and $N_H^\downarrow(L)=\sum_{\lambda_j+\lambda_k\le L}\lambda_j\lambda_k$ over ordered pairs. Suppose their ratio tends to a finite $\xi>1$ and set $\eta=(\xi-1)^{-1}$. For the actual equilibrium inverse temperature and Gibbs state,
--
--   $$\frac{E\beta(E)}\eta\longrightarrow1,\qquad\frac{S(\gamma(E))}{\eta\log E}\longrightarrow1\quad(E\to\infty).$$
--
--   Consequently the single spectral remainder $R_H(x)=S(\gamma(x))/(\eta\log x)-1$ tends to zero. Signed semibounded spectra are allowed. These are the temperature and entropy parts of Theorem 3; its separate partition-prefactor assertion is deferred.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 38, Theorem 3, inverse-temperature and entropy asymptotics

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

attribute [local instance] Classical.propDecidable Classical.decEq

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Theorem 3, PDF pp.38--39, (7.6) and entropy conclusion only. Signed
semibounded spectra and multiplicities are retained. No existence of the
partition-function prefactor kappa is assumed or concluded here. -/
theorem gibbs_temperature_entropy_asymptotics {I : Type} [Countable I] [Infinite I]
    (H : Spectral.Hamiltonian I) (hG : H.gibbs) (xi : ℝ) (hxi : HasPairRatio H xi) :
    Tendsto (fun E => E * betaAtEnergy H E / entropyExponent xi) atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (fun E => equilibriumEntropyNats H E / (entropyExponent xi * Real.log E))
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (entropyRemainder H xi) atTop (𝓝 (0 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
