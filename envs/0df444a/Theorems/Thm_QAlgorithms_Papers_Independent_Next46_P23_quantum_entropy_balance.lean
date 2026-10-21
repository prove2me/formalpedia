-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_quantum_entropy_balance
-- name    : QAlgorithms.Papers.Independent.Next46.P23.quantum_entropy_balance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:50:00.094206+00:00
-- url     : https://prove2.me/theorems/364028e0-664d-45da-9e93-26598965c6ef
-- title:
--   §3.2: quantum entropy balance and mean production
-- statement:
--   Let $H=H^*$ and $\omega>0$ be a normalized state on a nonzero finite-dimensional complex Hilbert space. Set $\sigma=-i[H,\log\omega]$, $\sigma_s=\tau^s(\sigma)$ and, for $t>0$, $\Sigma^t=t^{-1}\int_0^t\sigma_sds$. With the nonpositive relative-entropy convention, $$S(\omega_t\mid\omega)=-\int_0^t\omega(\sigma_s)ds,\qquad\omega(\Sigma^t)=\frac1t\int_0^t\omega(\sigma_s)ds\ge0.$$ The balance identity holds for every real $t$; TRI is not required.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 72, §3.2: quantum entropy balance and mean production

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Quantum entropy balance and nonnegative mean production, source PDF p.72 (3.3)--(3.4). -/
theorem quantum_entropy_balance [Nonempty I] (H omega : Mat I) (hH : H.IsHermitian)
    (homega : QAlgorithms.IsDensityMatrix omega) (hfaithful : omega.PosDef) :
    (∀ t : ℝ, signedRelativeEntropy (evolved H omega t) omega =
      ((-(∫ s in (0 : ℝ)..t, ev omega (tau H s (entropyProduction H omega))) : ℝ) : EReal)) ∧
    (∀ t : ℝ, 0 < t → ev omega (averagedProduction H omega t) =
      t⁻¹ * ∫ s in (0 : ℝ)..t, ev omega (tau H s (entropyProduction H omega)) ∧
        0 ≤ ev omega (averagedProduction H omega t)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
