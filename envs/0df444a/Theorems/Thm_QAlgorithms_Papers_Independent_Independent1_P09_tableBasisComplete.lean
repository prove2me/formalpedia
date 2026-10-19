-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_tableBasisComplete
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.tableBasisComplete
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:27:05.755446+00:00
-- url     : https://prove2.me/theorems/c97c02e7-6d2d-447e-88d8-204e59ace5eb
-- title:
--   Real basis completeness, including tensor products
-- statement:
--   Let $B_1,\ldots,B_{16}$ be the real $4\times4$ Pauli transfer matrices of Table I. Form the $16\times16$ matrix $A$ whose columns are their column vectorizations. Then $A$ is invertible. For every $n\ge0$ and every real matrix $E$ on the $n$-wire Pauli coordinate space, there is exactly one real coefficient array $q$ such that
--   $$E=\sum_{i_1,\ldots,i_n=1}^{16}q_{i_1,\ldots,i_n}\,
--    B_{i_1}\otimes\cdots\otimes B_{i_n}.$$
--   For $n=0$ this is the scalar basis. The span concerns signed maps, including trace-decreasing branches, rather than only channels. It supplies the algebraic completeness needed for cancellation.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, §VII; Appendix D, PDF p. 5. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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














































/-- PDF pp.4–5,13: Table I spans all real operations, including tensor products and n=0. -/
theorem tableBasisComplete :
    IsUnit (localFlat localTransfer) ∧
    ∀ n : ℕ, ∀ E : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ,
      ∃! q : (Fin n → Fin 16) → ℝ,
        E = ∑ i, q i • tensorOperation (fun _ => localTransfer) i := by sorry

















end QAlgorithms.Papers.Independent.Independent1.P09
