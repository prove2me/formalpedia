-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_polarPartialIsometry_replacement
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.polarPartialIsometry_replacement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:20:44.085935+00:00
-- url     : https://prove2.me/theorems/1e0e2f95-5436-4fa5-a433-2241b84e62c2
-- title:
--   Replacing a normalized operator by a maximal partial isometry
-- statement:
--   Let $S,C$ be nonzero finite-dimensional complex Hilbert spaces, let $E:S\to C$ and $A:C\to S$ be linear operators, and let $\rho$ be a density operator on $S$. Suppose $A^\dagger A\leq I$, $\operatorname{tr}(E\rho E^\dagger)=1$, and $|\operatorname{tr}(AE\rho)|^2\geq1-\eta$. There is a maximal partial isometry $W:S\to C$ satisfying
--
--   $$|\operatorname{tr}(AW\rho)|^2\geq1-2\eta.$$
--
--   Maximality means that either $W^\dagger W$ or $WW^\dagger$ is the identity, covering both dimension orders. The operator $E$ need not be a contraction.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 10, Lemma 11, Eqs.(91)–(94)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.10, Lemma 11, Eqs.(91)--(94). Source correction: rho is on S, the domain
of E, rather than the printed B(C); every product in the hypothesis forces this.
The operator E need not be a contraction. Maximality covers both dimension orders. -/
theorem polarPartialIsometry_replacement {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (E : Matrix J I ℂ) (A : Matrix I J ℂ) (eta : ℝ)
    (hgood : 1 - eta ≤ operatorFe rho (A * E))
    (hcontract : (1 - Aᴴ * A).PosSemidef) (hnorm : (E * rho * Eᴴ).trace = 1) :
    ∃ W : Matrix J I ℂ, IsMaximalPartialIsometry W ∧
      1 - 2 * eta ≤ operatorFe rho (A * W) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
