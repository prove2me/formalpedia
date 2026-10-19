-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_pairReading_noAdditionalLogicals
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.pairReading_noAdditionalLogicals
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:42:52.223247+00:00
-- url     : https://prove2.me/theorems/1dea717a-1a93-4543-82d5-437b3bcc3336
-- title:
--   Lemma 3.2: no extra logical qubits
-- statement:
--   Let binary check matrices $H_X,H_Z$ satisfy $H_XH_Z^T=0$, and let $D_X,D_Z$ be the prescribed pair-reading matrices of Eq. (2). Write $L_Z=\ker H_X/\operatorname{im}H_Z^T$ and $L_X=\ker H_Z/\operatorname{im}H_X^T$. Then
--
--   $$L_Z(D_X,D_Z)\cong L_Z(H_X,H_Z),\qquad L_X(D_X,D_Z)\cong L_X(H_X,H_Z).$$
--
--   The deformation of two identical memories therefore retains exactly $k$ logical qubits, with no additional logical classes. All spaces and isomorphisms are over $\mathbb F_2$.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, Lemma 3.2, PDF p. 18. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

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















/-- Lemma 3.2, PDF pp.18–19: the pair deformation has the original k logical qubits,
with the displayed identification of its logical space, rather than the initial 2k.
LDPC is irrelevant to this finite spatial identity. -/
theorem pairReading_noAdditionalLogicals {n mx mz : ℕ}
    (HX : Matrix (Fin mx) (Fin n) F2) (HZ : Matrix (Fin mz) (Fin n) F2)
    (css : HX * HZ.transpose = 0) :
    Nonempty (logicalSpace (readingX HX pairPattern) (readingZ HX HZ pairPattern) ≃ₗ[F2]
      logicalSpace HX HZ) ∧
    Nonempty (logicalSpace (readingZ HX HZ pairPattern) (readingX HX pairPattern) ≃ₗ[F2]
      logicalSpace HZ HX) := by sorry
































end QAlgorithms.Papers.Independent.Independent1.P06
