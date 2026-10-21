-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_phase_partial_dephasing
-- name    : QAlgorithms.Papers.Independent.Next46.P29.phase_partial_dephasing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:20:42.913886+00:00
-- url     : https://prove2.me/theorems/aaee3f39-f75b-4c35-9874-b9cf435ddfc2
-- title:
--   Uniform bounded phase tokens induce partial dephasing
-- statement:
--   Let $N\ge0$ be an integer. The token is $|e_N\rangle=(N+1)^{-1/2}\sum_{n=0}^N|n\rangle$, and the message uses the number states $|0\rangle,|1\rangle$. Apply the same number action $U(\theta)|n\rangle=e^{-in\theta}|n\rangle$ to both registers and average their joint state using $d\theta/(2\pi)$. Let $\mathcal E_N$ be this actual encoding, and $\mathcal R_N$ the covariant token measurement with density $(N+1)|\theta\rangle\langle\theta|$, followed by the inverse message rotation. The token is normalized, both maps are channels, and for every qubit density operator,
--
--   $$\mathcal R_N\mathcal E_N(\rho)=\frac{N}{N+1}\rho+\frac{1}{N+1}\Delta(\rho),\qquad\Delta(\rho)=\operatorname{diag}(\rho_{00},\rho_{11}).$$
--
--   At $N=0$ the result is complete dephasing.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 11, §IV.A: phase-token partial dephasing, Eq.(55)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.11, Eq.(55): the constructed phase encoding and covariant decoding
produce partial dephasing, with its exact cutoff-dependent coefficient.
Printed Eq.(50) omits the factor `(N+1)^(-2)` in the squared character sum;
the normalized Eq.(48) token used here restores it, since self-overlap is one.
The final Eq.(55) channel is unchanged. -/
theorem phase_partial_dephasing (N : ℕ) :
    IsState (phaseKet N) ∧ IsChannel (phaseEncoding N) ∧ IsChannel (phaseRecovery N) ∧
    ∀ rho, IsDensityMatrix rho →
      phaseRecovery N (phaseEncoding N rho) =
        ((N : ℝ) / (N + 1) : ℂ) • rho +
        ((1 : ℝ) / (N + 1) : ℂ) • dephasing rho := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
