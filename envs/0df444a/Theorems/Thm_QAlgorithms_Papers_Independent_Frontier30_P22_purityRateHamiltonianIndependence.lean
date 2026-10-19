-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P22_purityRateHamiltonianIndependence
-- name    : QAlgorithms.Papers.Independent.Frontier30.P22.purityRateHamiltonianIndependence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:23:01.360452+00:00
-- url     : https://prove2.me/theorems/a9f25015-73d6-418e-a6fd-27ee888ed25f
-- title:
--   Purity rate and instantaneous Hamiltonian independence
-- statement:
--   Let $\mathcal H$ be a nonzero complex Hilbert space with any orthonormal Hilbert basis, $H$ a densely defined self-adjoint Hamiltonian, and $(F_\alpha)$ bounded jumps. At the current density $R=\rho(t)$, require that $R$ preserve $\operatorname{Dom}(H)$ and that the actual commutator $HR-RH$ on that domain extend to a trace-class bounded operator $C$. Separate products $HR$ and $RH$ need not be trace class. Let the trace-class curve have right trace-norm derivative $-iC+\mathcal L(R)$ at $t$. The dissipator has the one-half anticommutator normalization; its jump sum converges in trace norm and both expanded trace series converge absolutely. Then
--   $$
--   \dot p(t)=2\operatorname{Re}\operatorname{Tr}(R[-iC+\mathcal L(R)])=2\operatorname{Re}\operatorname{Tr}(R\mathcal L(R))
--   =2\sum_\alpha\left(\operatorname{Re}\operatorname{Tr}(RF_\alpha RF_\alpha^\dagger)-\operatorname{Re}\operatorname{Tr}(R^2F_\alpha^\dagger F_\alpha)\right),\qquad \operatorname{Tr}(RC)=0.
--   $$
--   Here $p(\rho)=\operatorname{Tr}(\rho^2)$, and a density is positive trace class with trace one. This is instantaneous Hamiltonian independence at a fixed state; no comparison of differently controlled trajectories is asserted.
-- source:
--   Conditions for strictly purity-decreasing quantum Markovian dynamics, arXiv:quant-ph/0411119v2, PDF p. 2, Section II, Eq. (7)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P22

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P22

local notation "FD" => QAlgorithms.Papers.Independent.Dependency50.P16.LindbladData

local notation "finiteG" => QAlgorithms.Papers.Independent.Dependency50.P16.gkslGenerator

local notation "finiteEvolution" => QAlgorithms.Papers.Independent.Dependency50.P16.semigroupEvolution

section HilbertPurity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.2, Section II, first line of Eq.(7): instantaneous purity rate and
Hamiltonian independence for bounded jumps, on an arbitrary Hilbert space.
The Hamiltonian may be unbounded: its genuine self-adjoint domain and actual
trace-class commutator are explicit; separate products need not be trace class.
Infinite jump families have explicit trace-norm and scalar-trace convergence.
Printed: the expanded last line of (7), repeated in (17), omits a factor 2.
Changed: the expansion has factor 2, as in (2),(4), first line of (7), and (14).
Why: differentiating Tr(rho squared) produces two equal cyclic-trace terms.
No assertion compares different controlled trajectories at later times. -/
theorem purityRateHamiltonianIndependence [Nontrivial H] {I A : Type*}
    (b : HilbertBasis I ℂ H) (K : SelfAdjointHamiltonian (H := H))
    (F : A → H →L[ℂ] H) (rho : ℝ → H →L[ℂ] H) (t : ℝ)
    (hstate : TC.IsPositive (rho t) ∧ TC.operatorTrace b (rho t) = 1)
    (C : H →L[ℂ] H) (hC : RegularHamiltonianCommutator K (rho t) C)
    (L : H →L[ℂ] H)
    (hL : QAlgorithms.Papers.Independent.Dependency50.P39.TraceHasSum
      (fun a => boundedJumpTerm (F a) (rho t)) L)
    (hgain : Summable (fun a => TC.operatorTrace b
      (rho t * F a * rho t * (F a).adjoint)))
    (hloss : Summable (fun a => TC.operatorTrace b
      (rho t * rho t * (F a).adjoint * F a)))
    (hrho : HasTraceDerivative rho
      (-Complex.I • C + L) t) :
    HasDerivWithinAt (fun s => hilbertPurity b (rho s))
      (2 * (TC.operatorTrace b (rho t * L)).re) (Set.Ici t) t ∧
    TC.operatorTrace b (rho t * C) = 0 ∧
    2 * (TC.operatorTrace b
      (rho t * (-Complex.I • C + L))).re =
      2 * (TC.operatorTrace b (rho t * L)).re ∧
    2 * (TC.operatorTrace b (rho t * L)).re =
      2 * (∑' a, ((TC.operatorTrace b (rho t * F a * rho t * (F a).adjoint)).re -
        (TC.operatorTrace b (rho t * rho t * (F a).adjoint * F a)).re)) := by sorry

end HilbertPurity

end QAlgorithms.Papers.Independent.Frontier30.P22

end
