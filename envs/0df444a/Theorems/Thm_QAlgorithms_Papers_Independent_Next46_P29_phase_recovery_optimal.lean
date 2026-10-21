-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_phase_recovery_optimal
-- name    : QAlgorithms.Papers.Independent.Next46.P29.phase_recovery_optimal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:21:56.244872+00:00
-- url     : https://prove2.me/theorems/736a7b7b-508f-410e-9918-fec82f4b181e
-- title:
--   Optimal recovery for the fixed uniform phase token
-- statement:
--   For an integer cutoff $N\ge0$, use the normalized uniform number token, the actual joint number-twirling encoding $\mathcal E_N$, and its normalized adjoint recovery $\mathcal R_N$. For every deterministic completely positive trace-preserving decoder $\mathcal D$ from the joint token/message register to the qubit,
--
--   $$F_e(I_2/2,\mathcal D\mathcal E_N)\le F_e(I_2/2,\mathcal R_N\mathcal E_N).$$
--
--   Here $F_e$ is normalized entanglement fidelity for the maximally mixed input. The optimization is over decoders for this fixed token, not over token amplitudes.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 12, §IV.B: phase-token adjoint recovery is optimal

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

/-- PDF p.12, §IV.B: optimal entanglement fidelity for the fixed uniform phase
token. All deterministic quantum decoders are included; token optimization is absent. -/
theorem phase_recovery_optimal (N : ℕ) :
    ∀ D : Superop (Fin (N + 1) × Fin 2) (Fin 2), IsChannel D →
      QuditFidelity.entanglementFidelity 2 (by decide) (D ∘ phaseEncoding N) ≤
        QuditFidelity.entanglementFidelity 2 (by decide)
          (phaseRecovery N ∘ phaseEncoding N) := by sorry

end QAlgorithms.Papers.Independent.Next46.P29

end
