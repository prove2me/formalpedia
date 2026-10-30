-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P39_greenEfficiencyPartition
-- name    : QAlgorithms.Papers.Independent.Advance50.P39.greenEfficiencyPartition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:58:57.408207+00:00
-- url     : https://prove2.me/theorems/73567ff3-1cd4-4346-8ce0-f5072a59a1fe
-- title:
--   Additive Green-function partition with no initial trap population
-- statement:
--   Let a finite single-excitation transport model have $N\ge1$, $\hbar>0$, $\Gamma>0$, nonnegative trapping rates, a Hermitian coherent Hamiltonian and a trace-preserving Lindblad phonon term. Let $\rho_0$ be positive semidefinite with trace one. Set $H_{\rm recomb}=\hbar\Gamma I$, $H_{\rm trap}=\hbar\operatorname{diag}(\kappa_m)$, $\mathcal A X=-\{H_{\rm recomb}+H_{\rm trap},X\}/\hbar$, and $\mathcal M=\mathcal A+\mathcal R$. Suppose $\operatorname{Tr}(H_{\rm trap}\rho_0)=0$ and choose a finite process decomposition $\mathcal R=\sum_k\mathcal R_k$.
--
--   Both inverse superoperators exist; explicitly $(\mathcal A^{-1}X)_{mn}=-X_{mn}/(2\Gamma+\kappa_m+\kappa_n)$. The trapping flux is integrable and its efficiency satisfies
--   $$
--   \eta=\sum_k\eta_k,\qquad
--   \eta_k=-\frac2\hbar\operatorname{Tr}\!\left(H_{\rm recomb}\mathcal A^{-1}\mathcal R_k\mathcal M^{-1}\rho_0\right).
--   $$
--   This partitions the integrated trapping probability through the actual total dynamics and the specified processes. The source's Eq. (8) needs a minus sign, and its reference-term cancellation requires the initial-trap restriction stated later on p.5; these corrections are disclosed for independent moderation.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, PDF p. 3, §III, Eqs.(2),(9): Green-function additive efficiency partition

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1--3, Eqs. (2),(9), with initial-trap exclusion stated on p.5.
Printed Eq. (8) has plus; M=A+R forces minus. Eq. (9) has the correct negative
sign. The reference-only cancellation also requires Tr(H_trap rho0)=0, otherwise
an omitted reference-only trapping term remains. Independent moderation is pending. 
Source-model correction: printed Eq.(5) has A_m A_n^dagger loss products;
changed here to A_n^dagger A_m in canonical GKSL form, because the printed
order fails the source excitation-preservation assumption. The microscopic
phonon-rate formula remains deferred; see the item correction record. -/
theorem greenEfficiencyPartition {n r : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0)
    (hnoTrap : (trappingHamiltonian D * rho0).trace = 0)
    (parts : Fin r → Superoperator n)
    (hparts : ∑ k, parts k = transportRemainder D) :
    IsUnit (transportGenerator D) ∧
    (∀ X, referenceInverse D (referenceGenerator D X) = X ∧
      referenceGenerator D (referenceInverse D X) = X) ∧
    IntegrableOn (fun t => lossFlux D (trappingHamiltonian D)
      (transportState (transportGenerator D) rho0 t)) (Set.Ici 0) ∧
    efficiency D rho0 = ∑ k, greenContribution D (parts k) rho0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P39

end
