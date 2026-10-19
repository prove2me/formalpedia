-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_compensationUnique
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.compensationUnique
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:27:52.446304+00:00
-- url     : https://prove2.me/theorems/5d3c523a-d8d5-4434-986e-9fbab7706572
-- title:
--   Compensation existence and uniqueness
-- statement:
--   Let $E_0,E$ be ideal and native real Pauli transfer matrices on $n$ wires. On each wire let $B_{j,1},\ldots,B_{j,16}$ be a complete real operation basis with invertible synthesis matrix $A_j$. Fix any real $\lambda$. Define $q$ by applying the inverse tensor synthesis matrix to the interleaved coordinates of $E_0-\lambda E$. Then
--   $$E_0=\lambda E+\sum_{\mathbf i}q_{\mathbf i}\bigotimes_jB_{j,i_j},$$
--   and this coefficient array is unique for the chosen $\lambda$. No inverse of $E$ is required. This is the algebraic compensation witness; physical sampling is conditional on the branch realizations.
--
--   **Correction to the printed source.**
--
--   Printed: Eq. (2), PDF p.5, stacks each basis matrix by columns. D3, PDF p.13, instead starts with E_{I...I,I...I}, E_{I...I,I...X}, varying the column index before the row index.
--
--   Corrected: Use column-then-row local index pairs, evaluating E(row,column), in both the tensor synthesis matrix and the interleaved target vector. This swaps the local row/column order printed in D3; all tensor factors and basis-operation labels retain their order.
--
--   Reason: D1 and the inverse-coordinate construction use the synthesis matrices defined by Eq. (2). Their target vector must use the same ordering. Correcting only D3 makes those formulas consistent; it changes neither the represented operation nor any coefficient-mass bound. Independent moderation must verify this source correction.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, §VIII, pp.5–6, PDF p. 5. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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




















































/-- PDF pp.5–6, §VIII: compensation coefficients exist uniquely for fixed real lambda.
Coordinates use Eq. (2): printed D3 has its local row/column order reversed; swapping
those pairs preserves D1 and changes no compensation target. -/
theorem compensationUnique {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j)))
    (ideal native : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) (lam : ℝ) :
    ideal = lam • native + ∑ i, tensorCoordinates B (ideal-lam • native) i • tensorOperation B i ∧
    ∃! q : (Fin n → Fin 16) → ℝ, ideal = lam • native + ∑ i, q i • tensorOperation B i := by sorry











end QAlgorithms.Papers.Independent.Independent1.P09
