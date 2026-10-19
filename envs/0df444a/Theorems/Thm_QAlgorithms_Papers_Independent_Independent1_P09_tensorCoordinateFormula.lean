-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_tensorCoordinateFormula
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.tensorCoordinateFormula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:26:48.478931+00:00
-- url     : https://prove2.me/theorems/29c5110b-65fa-4a70-a997-4a4873ae18a7
-- title:
--   Computed tensor coordinates
-- statement:
--   For wire $j=1,\ldots,n$, let $B_{j,i}$ ($i=1,\ldots,16$) be real $4\times4$ basis matrices and let $A_j$ be the square matrix with columns $\operatorname{vec}(B_{j,i})$. Assume each $A_j$ invertible. For a real $n$-wire map $E$, vectorize by interleaving each wire's column and row indices, using the column-first convention of Eq. (2), correcting the reversed local pairs in (D3), and define
--   $$q=(A_1\otimes\cdots\otimes A_n)^{-1}\operatorname{vec}_{\mathrm{int}}(E).$$
--   The tensor synthesis matrix is invertible and
--   $$E=\sum_{\mathbf i}q_{\mathbf i}\bigotimes_j B_{j,i_j};$$
--   every coefficient array representing $E$ equals this computed $q$. Empty tensors have scalar value one. This pins the construction rather than quantifying over unrelated coefficients.
--
--   **Correction to the printed source.**
--
--   Printed: Eq. (2), PDF p.5, stacks each basis matrix by columns. D3, PDF p.13, instead starts with E_{I...I,I...I}, E_{I...I,I...X}, varying the column index before the row index.
--
--   Corrected: Use column-then-row local index pairs, evaluating E(row,column), in both the tensor synthesis matrix and the interleaved target vector. This swaps the local row/column order printed in D3; all tensor factors and basis-operation labels retain their order.
--
--   Reason: D1 and the inverse-coordinate construction use the synthesis matrices defined by Eq. (2). Their target vector must use the same ordering. Correcting only D3 makes those formulas consistent; it changes neither the represented operation nor any coefficient-mass bound. Independent moderation must verify this source correction.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Appendix D (D1)–(D3), PDF p. 13. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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


















































/-- PDF p.13, Appendix D (D1)–(D3): computed inverse tensor coordinates and uniqueness.
Printed D3 varies columns first, contrary to Eq. (2); transpose its local index pairs
to match Eq. (2) and retain D1. No operation or coefficient ordering is otherwise changed. -/
theorem tensorCoordinateFormula {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j)))
    (E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) :
    IsUnit (tensorFlat B) ∧
    E = ∑ i, tensorCoordinates B E i • tensorOperation B i ∧
    ∀ q, E = ∑ i, q i • tensorOperation B i → q = tensorCoordinates B E := by sorry













end QAlgorithms.Papers.Independent.Independent1.P09
