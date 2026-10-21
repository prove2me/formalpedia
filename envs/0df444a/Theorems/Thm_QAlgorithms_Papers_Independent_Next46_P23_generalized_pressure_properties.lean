-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_generalized_pressure_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P23.generalized_pressure_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:57:36.817364+00:00
-- url     : https://prove2.me/theorems/ae8c2ea7-b548-4348-94d6-c0bf065b3087
-- title:
--   Proposition 3.12
-- statement:
--   Let a finite-dimensional family $(H_X,\omega_X,\Phi_X)$ have faithful normalized states, self-adjoint currents, equilibrium invariance, and $\sigma_X=\sum_jX_j\Phi_X^{(j)}$. Define $e_t(X,Y)=\log\operatorname{tr}\exp(\log\omega_X+\sum_jY_j\int_0^t\Phi_{X,-s}^{(j)}ds)$. Then $$e_t(X,Y)=\sup_\nu\left[S(\nu\mid\omega_X)+\sum_jY_j\int_0^t\nu(\Phi_{X,-s}^{(j)})ds\right],\quad e_{-t}(X,Y)=e_t(X,X-Y).$$ It is convex and real analytic in $Y$. Its gradient at zero is the integrated negative-time current mean; its Hessian is the double integral of the centered Kubo–Mori current correlation, with indices and negative times as in (3.20). If reversals also make every chosen flux odd, then $e_{-t}=e_t$ and $e_t(X,Y)=e_t(X,X-Y)$. These are all five assertions.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 86, Proposition 3.12

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

/-- Proposition3.12, all five clauses, source PDF p.86. TRI is conditional in clause5. -/
theorem generalized_pressure_properties [Nonempty I] {n : ℕ} (F : FluxFamily I n) :
    (∀ X t Y, (generalizedPressure F X t Y : EReal) =
      sSup {v | ∃ nu : Mat I, QAlgorithms.IsDensityMatrix nu ∧
        v = signedRelativeEntropy nu (F.omega X) +
          ((∑ j, Y j * ∫ s in (0 : ℝ)..t, ev nu (tau (F.H X) (-s) (F.Phi X j)) : ℝ) : EReal)}) ∧
    (∀ X t, ConvexOn ℝ Set.univ (generalizedPressure F X t) ∧
      AnalyticOnNhd ℝ (generalizedPressure F X t) Set.univ) ∧
    (∀ X t Y, generalizedPressure F X (-t) Y = generalizedPressure F X t (X-Y)) ∧
    (∀ X t (j k : Fin n),
      fderiv ℝ (generalizedPressure F X t) 0 (Pi.single j 1) =
        ∫ s in (0 : ℝ)..t, ev (F.omega X) (tau (F.H X) (-s) (F.Phi X j)) ∧
      fderiv ℝ (fun Y => fderiv ℝ (generalizedPressure F X t) Y (Pi.single j 1)) 0 (Pi.single k 1) =
        ∫ s in (0 : ℝ)..t, ∫ u in (0 : ℝ)..t,
          (kuboMori (F.omega X) (tau (F.H X) (-s) (F.Phi X k))
            (tau (F.H X) (-u) (F.Phi X j))).re -
          ev (F.omega X) (tau (F.H X) (-s) (F.Phi X k)) *
            ev (F.omega X) (tau (F.H X) (-u) (F.Phi X j))) ∧
    (FluxTRI F → ∀ X t Y,
      generalizedPressure F X (-t) Y = generalizedPressure F X t Y ∧
      generalizedPressure F X t Y = generalizedPressure F X t (X-Y)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
