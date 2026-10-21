-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_finite_green_kubo
-- name    : QAlgorithms.Papers.Independent.Next46.P23.finite_green_kubo
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:59:15.927995+00:00
-- url     : https://prove2.me/theorems/a55ee7ac-27ab-441f-b060-dca057d6e631
-- title:
--   Proposition 3.14
-- statement:
--   For a continuously differentiable finite-dimensional family with faithful normalized states, equilibrium invariance and chosen flux relation, assume that at every parameter there is a reversal preserving the state and reversing the chosen fluxes. Let $\omega=\omega_0$, $\tau=\tau_0$ and $\Phi=\Phi_0$. Then for $t>0$, $$L^t_{jk}=\frac12\int_{-t}^t\langle\Phi^{(k)}\mid\tau^s(\Phi^{(j)})\rangle_\omega\left(1-\frac{|s|}{t}\right)ds,\qquad L^t_{jk}=L^t_{kj}.$$ The pairing is Kubo–Mori, not ordinary multiplication. The integral is real for these Hermitian currents.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 88, Proposition 3.14

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

/-- Proposition3.14, triangular Kubo--Mori Green--Kubo formula and ORR; source PDF p.88. -/
theorem finite_green_kubo [Nonempty I] {n : ℕ} (F : FluxFamily I n) (hF : FluxC1 F)
    (htri : FluxTRI F) (t : ℝ) (ht : 0 < t) :
    (∀ j k, kineticCoefficient F t j k = (1/2 : ℝ) * ∫ s in (-t)..t,
      (kuboMori (F.omega 0) (F.Phi 0 k) (tau (F.H 0) s (F.Phi 0 j))).re * (1-|s|/t)) ∧
    (∀ j k, kineticCoefficient F t j k = kineticCoefficient F t k j) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
