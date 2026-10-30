-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P39_susceptibilityDerivative
-- name    : QAlgorithms.Papers.Independent.Advance50.P39.susceptibilityDerivative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:02:12.697847+00:00
-- url     : https://prove2.me/theorems/81c0c3ab-1e31-4f71-bb9a-020bb763ac63
-- title:
--   Real process susceptibilities reproduce the master-equation velocity
-- statement:
--   Let $\mathcal M=\sum_k\mathcal M_k$ be a finite process decomposition of the constant finite-dimensional transport generator, with positive recombination, nonnegative trapping, Hermitian coherent evolution and trace-preserving Lindblad phonon dynamics. Fix a positive semidefinite trace-one matrix $\rho_0$ independently of all process multipliers. Put $\rho(t)=e^{t\mathcal M}\rho_0$ and, varying only the real multiplier of process $k$, define $\rho_{k,\lambda}(t)=\exp\!\left(t[\lambda\mathcal M_k+\sum_{j\ne k}\mathcal M_j]\right)\rho_0$.
--
--   For $t>0$, each family is differentiable at $\lambda=1$, with
--   $$
--   S_k(t):=\left.\frac{\partial\rho_{k,\lambda}(t)}{\partial\lambda}\right|_{\lambda=1}
--   =\int_0^t e^{(t-s)\mathcal M}\mathcal M_k e^{s\mathcal M}\rho_0\,ds,
--   \qquad
--   \frac{d\rho(t)}{dt}=\frac1t\sum_k S_k(t)=\mathcal M\rho(t).
--   $$
--   The derivatives have complex matrix outputs but real multiplier domain. This expresses the actual scaled-generator susceptibility, without assuming individual generators commute or that arbitrary negative multipliers remain physical.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, PDF p. 5, §V: scalar process susceptibilities and the master equation

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, unnumbered identity following Eq. (10): d rho/dt=(1/t) sum partial_k rho.
Differentiability at one is explicit, so totalized deriv cannot conceal failure.
The scaled generator need not remain physical for every negative multiplier. 
Source-model correction: printed Eq.(5) has A_m A_n^dagger loss products;
changed here to A_n^dagger A_m in canonical GKSL form, because the printed
order fails the source excitation-preservation assumption. The microscopic
phonon-rate formula remains deferred; see the item correction record. -/
theorem susceptibilityDerivative {n r : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0)
    (parts : Fin r → Superoperator n) (hparts : ∑ k, parts k = transportGenerator D)
    (t : ℝ) (ht : 0 < t) :
    (∀ k, HasDerivAt (fun lambda : ℝ => processScaledState parts rho0 k lambda t)
      (∫ s in (0 : ℝ)..t,
        insertionIntegrand (transportGenerator D) (parts k) rho0 t s) 1) ∧
    HasDerivAt (transportState (transportGenerator D) rho0)
      ((t⁻¹ : ℂ) • ∑ k, susceptibility parts rho0 k t) t ∧
    ((t⁻¹ : ℂ) • ∑ k, susceptibility parts rho0 k t) =
      transportGenerator D (transportState (transportGenerator D) rho0 t) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P39

end
