-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_tensor_homology_kunneth
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.tensor_homology_kunneth
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:44:09.620864+00:00
-- url     : https://prove2.me/theorems/4b0147b0-1f79-4998-b7e1-14b25d5fb17b
-- title:
--   Lemma 2.7: Kunneth isomorphism
-- statement:
--   Let $C_\bullet,D_\bullet$ be finite based chain complexes over $\mathbb F_2$, and let $l\in\mathbb Z$. Their tensor complex has differential $\partial_C\otimes I+I\otimes\partial_D$. There exists an $\mathbb F_2$-linear isomorphism
--
--   $$H_l(C_\bullet\otimes D_\bullet)\cong\bigoplus_{i\in\mathbb Z} H_i(C_\bullet)\otimes_{\mathbb F_2}H_{l-i}(D_\bullet).$$
--
--   The direct sum is algebraic; the finite based complexes have only finitely many nonzero graded components. No particular isomorphism or representative map is asserted.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, Lemma 2.7, PDF p. 12. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

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


/-- Lemma 2.7 (Kunneth formula), PDF p.12: homology of the finite based binary
 tensor complex is isomorphic to the direct sum of tensor products of homologies.
The index j = l - i reindexes exactly the source condition i + j = l. This asserts
existence of an isomorphism; the canonical representative map of Lemma 2.8 is separate. -/
theorem tensor_homology_kunneth (C D : Surgery.BasedBinaryComplex) (l : ℤ) :
    Nonempty (Surgery.Homology (Surgery.tensorComplex C D) l ≃ₗ[F2]
      DirectSum ℤ (fun i : ℤ => TensorProduct F2
        (Surgery.Homology C i) (Surgery.Homology D (l - i)))) := by sorry













































end QAlgorithms.Papers.Independent.Independent1.P06
