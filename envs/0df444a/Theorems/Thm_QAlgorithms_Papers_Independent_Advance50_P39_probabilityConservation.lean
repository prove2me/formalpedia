-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P39_probabilityConservation
-- name    : QAlgorithms.Papers.Independent.Advance50.P39.probabilityConservation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:57:41.880087+00:00
-- url     : https://prove2.me/theorems/837791c3-a352-4cb1-81db-48fcd8aecbe9
-- title:
--   Trapping and recombination exhaust the initial excitation
-- statement:
--   Let the single-excitation space have $N\ge1$ sites. Let $\hbar>0$, $\Gamma>0$, and $\kappa_m\ge0$. Let $H$ be a Hermitian Hamiltonian, including any Lamb shift, and let $L_j$ be a finite family of Lindblad jump matrices with their rates absorbed. Write $\mathcal R X=-i[H,X]/\hbar+\sum_j(L_jXL_j^\dagger-\{L_j^\dagger L_j,X\}/2)$, $H_{\rm recomb}=\hbar\Gamma I$, $H_{\rm trap}=\hbar\operatorname{diag}(\kappa_m)$, and $\mathcal M X=\mathcal R X-\{H_{\rm recomb}+H_{\rm trap},X\}/\hbar$. Starting from a positive semidefinite matrix $\rho_0$ of trace one, set $\rho(t)=e^{t\mathcal M}\rho_0$, without renormalizing the surviving excitation block.
--
--   The trajectory and both loss fluxes are integrable on $[0,\infty)$, the surviving population tends to zero, and
--   $$
--   \eta+\bar\eta=1,\qquad
--   \eta=\frac2\hbar\int_0^\infty\operatorname{Tr}(H_{\rm trap}\rho(t))\,dt,\qquad
--   \bar\eta=\frac2\hbar\int_0^\infty\operatorname{Tr}(H_{\rm recomb}\rho(t))\,dt.
--   $$
--   Thus the initial excitation is ultimately trapped or recombines. Traces in these physical fluxes are real; Lean takes their real parts.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, PDF p. 2, §II: trapping plus recombination probability equals one

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, following Eq. (6): eta+eta_bar=1 and eventual loss. Decay and
integrability are conclusions. The intended trace-preserving Lindblad reading
is used; the literal Eq. (5) defect is deferred separately. 
Source-model correction: printed Eq.(5) has A_m A_n^dagger loss products;
changed here to A_n^dagger A_m in canonical GKSL form, because the printed
order fails the source excitation-preservation assumption. The microscopic
phonon-rate formula remains deferred; see the item correction record. -/
theorem probabilityConservation {n : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0) :
    IntegrableOn (transportState (transportGenerator D) rho0) (Set.Ici 0) ∧
    IntegrableOn (fun t => lossFlux D (trappingHamiltonian D)
      (transportState (transportGenerator D) rho0 t)) (Set.Ici 0) ∧
    IntegrableOn (fun t => lossFlux D (recombinationHamiltonian D)
      (transportState (transportGenerator D) rho0 t)) (Set.Ici 0) ∧
    Tendsto (fun t => (transportState (transportGenerator D) rho0 t).trace.re)
      atTop (nhds 0) ∧ efficiency D rho0 + deficiency D rho0 = 1 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P39

end
