-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_matchingSelfDual_transversalS
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.matchingSelfDual_transversalS
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:44:47.217293+00:00
-- url     : https://prove2.me/theorems/311794d2-c016-4da2-bb18-734ae4ff0f95
-- title:
--   Lemma B.4: self-dual matching code transversal S
-- statement:
--   Let $H\in\mathbb F_2^{m\times n}$ satisfy $HH^T=0$, defining a self-dual CSS code with $H_X=H_Z=H$. Let $E$ isometrically encode all $k$ logical qubits onto its entire codespace. Suppose matching binary supports $v_i\in\ker H$ satisfy $v_i\cdot v_j=\delta_{ij}$, and their physical X and Z products implement the corresponding logical $X_i,Z_i$ through $E$. There exists a physical Pauli correction $P$, independent of the encoded state, such that
--
--   $$P S^{\otimes n}E=E S^{\otimes k}.$$
--
--   Here $S=\operatorname{diag}(1,i)$, and $P$ includes its Pauli phase. The matrix equality holds on the entire encoded space, implementing S on every logical qubit.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, Lemma B.4, PDF p. 85. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
set_option autoImplicit false

/-!
# Fast and fault-tolerant logical measurements (arXiv:2510.14895v1)

Paper-local definitions and statement-only targets. Deferred nodes are recorded in the
assigned unit's HARD.md and GAPS.json. No operational fault-distance lower bound is
inferred from the open-boundary homology calculation.
-/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P06












































/-- Lemma B.4, PDF p.85: the specified matching paired representatives admit physical
transversal S implementing S on every logical qubit after a state-independent Pauli
correction. The isometric encoder fixes the logical X and Z conventions. -/
theorem matchingSelfDual_transversalS {n m k : ℕ}
    (H : Matrix (Fin m) (Fin n) F2) (selfOrthogonal : H * H.transpose = 0)
    (E : Matrix (Qubits n) (Qubits k) ℂ)
    (isometry : E.conjTranspose * E = 1)
    (codespace : LinearMap.range (Matrix.toEuclideanLin E) =
      cssCode (LinearMap.ker H.mulVecLin) (LinearMap.ker H.mulVecLin))
    (representatives : Fin k → Fin n → F2)
    (normalizer : ∀ i, H.mulVec (representatives i) = 0)
    (paired : ∀ i j, representatives i ⬝ᵥ representatives j = if i = j then 1 else 0)
    (logicalAction : ∀ i,
      binaryPauli true (representatives i) * E = E * qubitOp1 pauliX i ∧
      binaryPauli false (representatives i) * E = E * qubitOp1 pauliZ i) :
    ∃ correction : Stabilizer.PauliString n,
      correction.toMatrix * kronAll (fun _ : Fin n => phaseS) * E =
        E * kronAll (fun _ : Fin k => phaseS) := by sorry



end QAlgorithms.Papers.Independent.Independent1.P06
