-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_tableSynthesis
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.tableSynthesis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:27:11.085601+00:00
-- url     : https://prove2.me/theorems/12ee7c02-45e6-4960-be36-65fdefe6bde5
-- title:
--   Synthesis of the sixteen branch operations
-- statement:
--   Use the sixteen matrices $A_i$ in Table I, in their printed order, and the superoperators $\mathcal B_i(X)=A_iXA_i^\dagger$. Let $W_i$ be the corresponding printed word with $R_x=HS^3H$, $R_z=S^3$ and $\pi=|0\rangle\langle0|$. Words are matrix products, so their rightmost factor acts first. For every $i=1,\ldots,16$,
--   $$[W_i]=\mathcal B_i,\qquad [A](X):=AXA^\dagger.$$
--   The phase convention for $S$ is irrelevant at the superoperator level. The three primitive letters are $H,S,\pi$; postselection denotes the accepted branch, without renormalization. These equalities give physical words for the library. Linear independence is stated in the separate completeness item.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, Table I; §VII, PDF p. 5. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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













































/-- PDF pp.4–5, Table I: actual H,S,postselection words synthesize all sixteen branches. -/
theorem tableSynthesis : ∀ i : Fin 16, tableWordMap i = tableIBasis i := by sorry


















end QAlgorithms.Papers.Independent.Independent1.P09
