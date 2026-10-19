-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_cnotDecomposition
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.cnotDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:26:27.864713+00:00
-- url     : https://prove2.me/theorems/65081d90-846e-492a-a793-6cf0b13c11a2
-- title:
--   CNOT decomposition with mass nine
-- statement:
--   Let $X,Z,R_x,R_z,\pi_x=(I+X)/2,\pi_z=(I+Z)/2$ be the Table I matrices, let $[A](\rho)=A\rho A^\dagger$, and put the control in the first tensor factor. Then
--   $$\begin{aligned}
--   [\mathrm{CNOT}]={}&\tfrac12([I\otimes X]+[Z\otimes I]-[I\otimes R_x]
--   -[R_z\otimes I]-[Z\otimes R_x]-[R_z\otimes X])\\
--   &+[Z\otimes X]+[R_z\otimes R_x]+[I\otimes\pi_x]+[\pi_z\otimes I]
--   -[Z\otimes\pi_x]-[\pi_z\otimes X].
--   \end{aligned}$$
--   The twelve coefficients have absolute sum $6/2+6=9$. The identity holds on every operator; projective branches are unnormalized. It exhibits how local signed operations represent an entangling gate.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix B (B2), PDF p. 13. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
set_option autoImplicit false

/-! Endo, Benjamin and Li, arXiv:1712.09271v2; citations use PDF pages.
Source defects and construction deferrals are recorded in the assigned chunk. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P09

open ErrorMitigation
















































/-- PDF p.13, Appendix B (B2): first tensor factor is the CNOT control; coefficient mass nine. -/
theorem cnotDecomposition :
    (∀ X : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      conjSuperop cnot X = ∑ j : Fin 12, ((cnotTerms j).2 : ℂ) •
        conjSuperop (Matrix.kronecker (tableIMatrix (cnotTerms j).1.1)
          (tableIMatrix (cnotTerms j).1.2)) X) ∧
    (∑ j : Fin 12, |(cnotTerms j).2|) = 9 := by sorry















end QAlgorithms.Papers.Independent.Independent1.P09
