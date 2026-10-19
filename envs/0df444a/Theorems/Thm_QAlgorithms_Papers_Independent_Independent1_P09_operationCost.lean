-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_operationCost
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.operationCost
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:28:06.509868+00:00
-- url     : https://prove2.me/theorems/b88784b8-1bf6-47d6-bf59-d76c80cfc4cf
-- title:
--   Computed compensation cost bound
-- statement:
--   Let $B_{j,i}$ be real local library maps, let $A_j$ be their $16\times16$ synthesis matrices, and let $A_0$ be the synthesis matrix computed from Table I. Put $e_{\max}=\max_j\|A_j-A_0\|_{\max}$ and $s=s_{\min}(A_0)$. Let $O_0,O$ be target and native $n$-wire real operation matrices, with $e_O=\|O_0-O\|_{\max}$. If $e_{\max}<s/16$, compute $q$ by inverse tensor synthesis of $O_0-O$. Then
--   $$O_0=O+\sum_{\mathbf i}q_{\mathbf i}\bigotimes_j B_{j,i_j},\qquad
--   C_O=1+\sum_{\mathbf i}|q_{\mathbf i}|
--   \le1+\frac{16^{2n}e_O}{(s-16e_{\max})^n}.$$
--   The denominator is positive. This is a bound on the constructed $\lambda=1$ witness, without an assumed inverse-norm conclusion or any claim of optimality.
--
--   **Correction to the printed source.**
--
--   Printed: Eq. (2), PDF p.5, stacks each basis matrix by columns. D3, PDF p.13, instead starts with E_{I...I,I...I}, E_{I...I,I...X}, varying the column index before the row index.
--
--   Corrected: Use column-then-row local index pairs, evaluating E(row,column), in both the tensor synthesis matrix and the interleaved target vector. This swaps the local row/column order printed in D3; all tensor factors and basis-operation labels retain their order.
--
--   Reason: D1 and the inverse-coordinate construction use the synthesis matrices defined by Eq. (2). Their target vector must use the same ordering. Correcting only D3 makes those formulas consistent; it changes neither the represented operation nor any coefficient-mass bound. Independent moderation must verify this source correction.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, §X (3); Appendix G (G1)–(G4), PDF p. 15. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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


























































/-- PDF pp.7,15–16, (3),(G1)–(G4): computed lambda=1 compensation witness cost.
G uses D3 coordinates. Printed D3 reverses the local row/column order of Eq. (2);
swap those pairs to preserve D1. The cost bound is unchanged by this permutation. -/
theorem operationCost {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (ideal native : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ) :
    let e := (Finset.univ.sup fun j => Real.toNNReal
      (entryMax (localFlat (B j)-localFlat localTransfer)) : ℝ≥0)
    (e : ℝ) < leastSingular (by omega) (localFlat localTransfer)/16 →
      ideal = native + ∑ i, tensorCoordinates B (ideal-native) i • tensorOperation B i ∧
      1+coefficientMass (tensorCoordinates B (ideal-native)) ≤
        1+(16 : ℝ)^(2*n)*entryMax (ideal-native)/
          (leastSingular (by omega) (localFlat localTransfer)-16*(e : ℝ))^n := by sorry





end QAlgorithms.Papers.Independent.Independent1.P09
