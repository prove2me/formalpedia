-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P39_greenInverseEfficiency
-- name    : QAlgorithms.Papers.Independent.Advance50.P39.greenInverseEfficiency
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:58:24.894879+00:00
-- url     : https://prove2.me/theorems/75be7b62-f177-4e56-bd0b-4ad03a18dd46
-- title:
--   The inverse generator gives the integrated efficiency
-- statement:
--   Consider a finite $N\ge1$ single-excitation transport model with $\hbar>0$, uniform recombination rate $\Gamma>0$, nonnegative trapping rates $\kappa_m$, a Hermitian coherent Hamiltonian, and a finite trace-preserving Lindblad phonon generator $\mathcal R$ including the coherent part. Put $H_{\rm recomb}=\hbar\Gamma I$, $H_{\rm trap}=\hbar\operatorname{diag}(\kappa_m)$, and $\mathcal M X=\mathcal R X-\{H_{\rm recomb}+H_{\rm trap},X\}/\hbar$. For a positive semidefinite trace-one initial state $\rho_0$, use the unnormalized trajectory $\rho(t)=e^{t\mathcal M}\rho_0$.
--
--   Then $\mathcal M$ is invertible, the trajectory and trapping flux are integrable, and
--   $$
--   \int_0^\infty\rho(t)\,dt=-\mathcal M^{-1}\rho_0,\qquad
--   \eta=-\frac2\hbar\operatorname{Tr}(H_{\rm trap}\mathcal M^{-1}\rho_0).
--   $$
--   Here $\eta=(2/\hbar)\int_0^\infty\operatorname{Tr}(H_{\rm trap}\rho(t))\,dt$. The inverse acts on density matrices as a superoperator. This is the Green-function representation of energy-transfer efficiency; invertibility and convergence are conclusions.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, PDF p. 2, §III, Eq.(7): integrated efficiency from the inverse generator

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, Eq. (7): invertibility of M and its integrated Green function.
Invertibility and integrability are conclusions, not assumptions. 
Source-model correction: printed Eq.(5) has A_m A_n^dagger loss products;
changed here to A_n^dagger A_m in canonical GKSL form, because the printed
order fails the source excitation-preservation assumption. The microscopic
phonon-rate formula remains deferred; see the item correction record. -/
theorem greenInverseEfficiency {n : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0) :
    IsUnit (transportGenerator D) ∧
    IntegrableOn (transportState (transportGenerator D) rho0) (Set.Ici 0) ∧
    (∫ t in Set.Ici (0 : ℝ), transportState (transportGenerator D) rho0 t) =
      -(Ring.inverse (transportGenerator D) rho0) ∧
    IntegrableOn (fun t => lossFlux D (trappingHamiltonian D)
      (transportState (transportGenerator D) rho0 t)) (Set.Ici 0) ∧
    efficiency D rho0 = -(2 / D.hbar) *
      (trappingHamiltonian D * Ring.inverse (transportGenerator D) rho0).trace.re := by sorry

end QAlgorithms.Papers.Independent.Advance50.P39

end
