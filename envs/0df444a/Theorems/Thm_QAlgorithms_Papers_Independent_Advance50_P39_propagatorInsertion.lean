-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P39_propagatorInsertion
-- name    : QAlgorithms.Papers.Independent.Advance50.P39.propagatorInsertion
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:01:46.400247+00:00
-- url     : https://prove2.me/theorems/3f2bfba6-65d6-4b02-8696-6ca4933900e7
-- title:
--   Time-averaged generator insertions reproduce the master equation
-- statement:
--   Consider the finite constant transport generator $\mathcal M$ with positive recombination, nonnegative trapping, Hermitian coherent evolution, and trace-preserving Lindblad phonon dynamics, and a fixed positive semidefinite trace-one initial matrix $\rho_0$. Choose any finite decomposition $\mathcal M=\sum_k\mathcal M_k$ into complex-linear process maps. Write $\mathcal F(t,s)=e^{(t-s)\mathcal M}$ and $\rho(t)=\mathcal F(t,0)\rho_0$. For every $t>0$, each insertion integrand is integrable on $[0,t]$, and
--   $$
--   \frac{d\rho(t)}{dt}=\sum_k\frac1t\int_0^t
--   \mathcal F(t,s)\mathcal M_k\mathcal F(s,0)\rho_0\,ds
--   =\mathcal M\rho(t).
--   $$
--   This is the source's insertion representation of the master equation. The post-evolution and pre-evolution remain in their displayed order; individual process maps need not commute with the total generator.
-- source:
--   Role of quantum coherence in chromophoric energy transport, arXiv:0806.4725v2, PDF p. 5, §V, Eq.(10): time-averaged generator insertion equals the master equation

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Eq. (10): averaged insertions sum to the master-equation velocity.
No individual process is assumed to commute with M; t=0 is excluded. 
Source-model correction: printed Eq.(5) has A_m A_n^dagger loss products;
changed here to A_n^dagger A_m in canonical GKSL form, because the printed
order fails the source excitation-preservation assumption. The microscopic
phonon-rate formula remains deferred; see the item correction record. -/
theorem propagatorInsertion {n r : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0)
    (parts : Fin r → Superoperator n) (hparts : ∑ k, parts k = transportGenerator D)
    (t : ℝ) (ht : 0 < t) :
    (∀ k, IntervalIntegrable
      (fun s => insertionIntegrand (transportGenerator D) (parts k) rho0 t s) volume 0 t) ∧
    HasDerivAt (transportState (transportGenerator D) rho0)
      (∑ k, averagedInsertion (transportGenerator D) (parts k) rho0 t) t ∧
    (∑ k, averagedInsertion (transportGenerator D) (parts k) rho0 t) =
      transportGenerator D (transportState (transportGenerator D) rho0 t) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P39

end
