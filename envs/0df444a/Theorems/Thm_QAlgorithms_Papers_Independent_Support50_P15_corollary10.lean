-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_corollary10
-- name    : QAlgorithms.Papers.Independent.Support50.P15.corollary10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:42:47.698519+00:00
-- url     : https://prove2.me/theorems/5d1f9a2e-7701-421a-add8-ae44b6768e37
-- title:
--   Maximum heat capacity in finite dimension
-- statement:
--   For a Hermitian Hamiltonian $H$ in dimension $d\ge2$, define heat capacity as the derivative of its mean thermal energy at positive finite temperature, with zero endpoint values at $T=0,+\infty$. The thermal state at zero is the normalized projector onto the whole ground eigenspace, and at infinity it is $I/d$. For every $T\in[0,+\infty]$,
--
--   $$C_H(T)\le N(d)<N_d=\frac14\log^2(d-1)+1.$$
--
--   These extended thermal states are normalized and have zero surprisal variance at both endpoints. The positive-temperature energy derivative tends to zero as the temperature decreases to zero or increases to infinity. For every $d\ge2$ the first bound is attained at $T=1$ by $H=-\log\tau_d(r_d)$, where $r_d$ maximizes Eq. (7). In dimension one every Hermitian Hamiltonian has heat capacity zero at all temperatures. This is uniform over Hamiltonians and temperatures; tightness is existential.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 9, corollary10

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Corollary 10, PDF p.9: a uniform bound at every temperature, and existential tightness. -/
theorem corollary10 :
    (∀ (h : Matrix (Fin 1) (Fin 1) ℂ), h.IsHermitian → ∀ t : ℝ≥0∞, heatCapacity h t = 0) ∧
    (∀ d : ℕ, 2 ≤ d →
      (∀ h : Matrix (Fin d) (Fin d) ℂ, h.IsHermitian → ∀ t : ℝ≥0∞,
        IsDensityMatrix (gibbsAtTemperature h t) ∧ heatCapacity h t ≤ maxVariance d ∧ maxVariance d < easyVariance d) ∧
      (∀ h : Matrix (Fin d) (Fin d) ℂ, h.IsHermitian →
        Tendsto (deriv (thermalExpectedEnergy h)) atTop (nhds 0) ∧
        Tendsto (deriv (thermalExpectedEnergy h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        surprisalVariance (gibbsAtTemperature h 0) = 0 ∧ surprisalVariance (gibbsAtTemperature h ⊤) = 0) ∧
      (∃ h : Matrix (Fin d) (Fin d) ℂ, h.IsHermitian ∧
        h = -cfc Real.log (family d (optimalMass d)) ∧
        thermalFinite h 1 = family d (optimalMass d) ∧ heatCapacity h 1 = maxVariance d)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
