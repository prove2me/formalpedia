-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_thermalThermodynamicExtremality
-- name    : QAlgorithms.Papers.Independent.Next46.P27.thermalThermodynamicExtremality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:27:00.118246+00:00
-- url     : https://prove2.me/theorems/f7c01875-0e32-4e97-b826-e606ff2b8d18
-- title:
--   Thermal states maximize entropy at fixed energy and minimize energy at fixed entropy
-- statement:
--   Let $\beta>0$ and let $\rho_\beta=(1-e^{-\beta})\sum_{j\ge0}e^{-\beta j}|j\rangle\langle j|$ be the full Gibbs density. For any positive normalized trace-class density $X$, use the extended photon-number mean $E(X)=\sum_j j\langle j|X|j\rangle\in[0,+\infty]$ and extended von Neumann entropy $S(X)$ in nats. Then
--
--   $$E(X)=E(\rho_\beta)\ \Longrightarrow\ S(X)\le S(\rho_\beta),$$
--   $$S(X)=S(\rho_\beta)\ \Longrightarrow\ E(\rho_\beta)\le E(X).$$
--
--   Both comparisons range over all densities, rather than only displaced Gibbs states. The second comparison includes infinite-energy competitors.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 4, Section VI, paragraph following Eq.(14): thermal thermodynamic extremality

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF p.4, Section VI: the two thermodynamic extrema used in the
local-minimum discussion. Thermal states maximize entropy at fixed number energy
and minimize number energy at fixed entropy, among all normalized densities.
Extended energy and entropy retain infinite competitors without a real-tsum default. -/
theorem thermalThermodynamicExtremality (beta : ℝ) (hbeta : 0 < beta) :
    let rho := A.photonMeanThermalState (gibbsMean beta)
    (∀ X : B.FockOperator, B.IsDensity X → energy X = energy rho →
      A.fockEntropyNats X ≤ A.fockEntropyNats rho) ∧
    (∀ X : B.FockOperator, B.IsDensity X → A.fockEntropyNats X = A.fockEntropyNats rho →
      energy rho ≤ energy X) := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
