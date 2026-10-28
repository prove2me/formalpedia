-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_minimumFidelity_controls_entanglementFidelity
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.minimumFidelity_controls_entanglementFidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:16:56.201012+00:00
-- url     : https://prove2.me/theorems/74ddc596-aa7b-4ba3-a451-d9df2354d39e
-- title:
--   Minimum pure-state fidelity controls entanglement fidelity
-- statement:
--   Let $\mathcal E$ be a trace-preserving completely positive operation on a nonzero finite-dimensional complex Hilbert space, and let $V$ be a subspace. Suppose every unit vector $\psi\in V$ satisfies $\langle\psi|\mathcal E(|\psi\rangle\langle\psi|)|\psi\rangle\geq1-\eta$. For every density operator $\rho$ supported entirely in $V$,
--
--   $$F_e(\rho,\mathcal E)\geq1-\frac32\eta.$$
--
--   The error factor is independent of dimension, and no QAEP hypothesis is required.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 8, Theorem 2; Eq.(83), p.9

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF pp.8--9, Theorem 2, Eq.(83): the coefficient is 3/2. Support means the
whole range of rho lies in the subspace, and the hypothesis includes all normalized
superpositions, not just a basis. No QAEP hypothesis is used. -/
theorem minimumFidelity_controls_entanglementFidelity {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (P rho : Matrix I I ℂ) (hP : IsProjection P)
    (hrho : IsDensityMatrix rho) (hsupport : P * rho = rho)
    (E : Superop I I) (hE : IsChannel E) (eta : ℝ)
    (hminimum : ∀ psi : EuclideanSpace ℂ I, ‖psi‖ = 1 → act P psi = psi →
      1 - eta ≤ effectProb (pureDensity psi) (E (pureDensity psi))) :
    1 - (3 : ℝ) / 2 * eta ≤ fe rho E := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
