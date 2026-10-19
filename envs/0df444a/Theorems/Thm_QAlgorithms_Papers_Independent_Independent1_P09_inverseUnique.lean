-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P09_inverseUnique
-- name    : QAlgorithms.Papers.Independent.Independent1.P09.inverseUnique
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:27:24.657771+00:00
-- url     : https://prove2.me/theorems/1addd990-a51e-4150-939d-6eb905d67137
-- title:
--   Inverse-method coefficients and order
-- statement:
--   Let $E_0,E$ be invertible ideal and native real operation matrices. Let the local bases $B_{j,i}$ have invertible synthesis matrices, and define $N=EE_0^{-1}$. Then $NE_0=E$ and $N^{-1}=E_0E^{-1}$. The computed tensor coordinates $q$ of $E_0E^{-1}$ are the unique representation of $N^{-1}$, and
--   $$E_0=\left(\sum_{\mathbf i}q_{\mathbf i}\bigotimes_j B_{j,i_j}\right)E.$$
--   Thus the physical order is the native operation followed by its sampled correction. Both inverses have explicit hypotheses; the inverse noise need not itself be a channel.
--
--   **Correction to the printed source.**
--
--   Printed: Eq. (2), PDF p.5, stacks each basis matrix by columns. D3, PDF p.13, instead starts with E_{I...I,I...I}, E_{I...I,I...X}, varying the column index before the row index.
--
--   Corrected: Use column-then-row local index pairs, evaluating E(row,column), in both the tensor synthesis matrix and the interleaved target vector. This swaps the local row/column order printed in D3; all tensor factors and basis-operation labels retain their order.
--
--   Reason: D1 and the inverse-coordinate construction use the synthesis matrices defined by Eq. (2). Their target vector must use the same ordering. Correcting only D3 makes those formulas consistent; it changes neither the represented operation nor any coefficient-mass bound. Independent moderation must verify this source correction.
-- source:
--   Practical Quantum Error Mitigation for Near-Future Applications, arXiv:1712.09271v2, §VIII, pp.5–6, PDF p. 6. https://arxiv.org/abs/1712.09271v2 . PDF SHA-256: 6911d403c4bf7ec58c8dade31dfb949dd3b31bdeee17d4a1f85bb8f80e504bb7.

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





















































/-- PDF pp.5–6, §VIII: correction follows native map; both inverses guarded.
Coordinates use Eq. (2): printed D3 has its local row/column order reversed; swapping
those pairs preserves D1 and changes no inverse-method target. -/
theorem inverseUnique {n : ℕ}
    (B : Fin n → Fin 16 → Matrix (Fin 4) (Fin 4) ℝ)
    (complete : ∀ j, IsUnit (localFlat (B j)))
    (ideal native : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℝ)
    (hi : IsUnit ideal) (hn : IsUnit native) :
    let noise := native*ideal⁻¹
    noise*ideal = native ∧ noise⁻¹ = ideal*native⁻¹ ∧
    ideal = (∑ i, tensorCoordinates B (ideal*native⁻¹) i • tensorOperation B i)*native ∧
    ∃! q : (Fin n → Fin 16) → ℝ, noise⁻¹ = ∑ i, q i • tensorOperation B i := by sorry










end QAlgorithms.Papers.Independent.Independent1.P09
