-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P36_piPhaseOrthogonality
-- name    : QAlgorithms.Papers.Independent.Advance50.P36.piPhaseOrthogonality
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:53:23.375251+00:00
-- url     : https://prove2.me/theorems/26b76806-ef76-475e-bb71-fe911c7e6d25
-- title:
--   Local pi phase maps Psi2 to its orthogonal Psi4
-- statement:
--   Let $\alpha\ne0$ be a finite complex coherent amplitude and $\kappa=e^{-2|\alpha|^2}$. In the full two-mode Fock space let
--   $$
--   \Psi_2=\frac{|\alpha,\alpha\rangle-|-\alpha,-\alpha\rangle}{\sqrt{2(1-\kappa^2)}},\qquad
--   \Psi_4=\frac{|\alpha,-\alpha\rangle-|-\alpha,\alpha\rangle}{\sqrt{2(1-\kappa^2)}}.
--   $$
--   The coherent factors have their canonical coefficients and unit norms, and $\Psi_2,\Psi_4$ are normalized. The physical phase rotation on mode $B$ multiplies the number-basis coefficient at $(n_A,n_B)$ by $e^{-i\theta n_B}$, leaving mode $A$ untouched. It obeys
--   $$
--   (I_A\otimes U_B(\pi))\Psi_2=\Psi_4,\qquad \langle\Psi_2|\Psi_4\rangle=0.
--   $$
--   This orthogonalization holds for every nonzero finite amplitude in this family and is the structural reason for error-free ideal binary reading.
--
--   **Formalization Note** Equality of vectors uses canonical coherent phases. The missing $i$ in printed Eq. (8) is corrected to the unitary action required by Eqs. (12) and (15).
-- source:
--   Error free Quantum Reading by Quasi Bell State of Entangled Coherent States, arXiv:1108.4163v2, PDF p. 3, §IV, Eqs.(14)-(16)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P36

open QAlgorithms.Papers.Independent.Frontier30.P21
  (WordFock coherentWord CoherentWordRealized binaryErrorValues)

open scoped Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.3, Eqs.(15)-(16): a pi shift on B maps Psi2 exactly to Psi4,
which is orthogonal to Psi2, for every nonzero finite amplitude. Eq.(8) on p.2
prints exp(-theta a†a); exp(-i theta N) is used because Eqs.(12),(15) require
a unitary sign flip. Exact vector equality uses canonical coherent phases. -/
theorem piPhaseOrthogonality (alpha : ℂ) (halpha : alpha ≠ 0) :
    QuasiBellCoherentRealized alpha ∧
    ‖quasiBellState alpha 1‖ = 1 ∧ ‖quasiBellState alpha 3‖ = 1 ∧
    modeBPhaseShift Real.pi (quasiBellState alpha 1) = quasiBellState alpha 3 ∧
    inner (𝕜 := ℂ) (quasiBellState alpha 1) (quasiBellState alpha 3) = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P36

end
