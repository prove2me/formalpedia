-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_exact_phase_gate_update
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.exact_phase_gate_update
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:14:50.206077+00:00
-- url     : https://prove2.me/theorems/3a07133c-fd72-4546-8e64-bd268ef354d3
-- title:
--   Circuit simulation: controlled-phase gates update graph weights exactly
-- statement:
--   Let $N,D\ge1$, let $A,\Phi$ be admissible data, take final rotations $V=I$, and let $j\ne k$. For any real angle $\theta$, update the two symmetric entries of the selected edge to $(\Phi_{jk}+\theta)\bmod 2\pi\in[0,2\pi)$, leaving every other entry fixed. The resulting graph $\Phi'$ is admissible and
--
--   $$R(A,\Phi',I)=U_{jk}(\theta)R(A,\Phi,I).$$
--
--   If the raw MPS is nonzero, normalization gives the same equality for unit vectors. Negative input angles are allowed. The gate acts once on the unordered pair; the simple rule applies in the stated $V=I$ setting.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 3, Circuit simulation: controlled-phase gates update graph weights exactly

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF pp.3–4, circuit update: with V=I, phase gates are exact graph-weight updates.
The same equality is asserted for normalized states only when the raw MPS is nonzero. -/
theorem exact_phase_gate_update {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D)
    (A : Tensors N D) (G : PhaseGraph N) (j k : Fin N) (hjk : j ≠ k) (theta : ℝ) :
    ∃ Gnew : PhaseGraph N, Gnew.weight = updatedWeights G j k theta ∧
      rage A Gnew (fun _ => 1) = controlledPhaseAction j k (Complex.exp (Complex.I * (theta : ℂ)))
        (rage A G (fun _ => 1)) ∧
      (traceMPS A ≠ 0 → IsState (normalizeRageVector (rage A Gnew (fun _ => 1))) ∧
        normalizeRageVector (rage A Gnew (fun _ => 1)) =
          controlledPhaseAction j k (Complex.exp (Complex.I * (theta : ℂ)))
            (normalizeRageVector (rage A G (fun _ => 1)))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
