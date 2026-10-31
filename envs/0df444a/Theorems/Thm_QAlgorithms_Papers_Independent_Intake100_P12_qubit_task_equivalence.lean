-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_qubit_task_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.qubit_task_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:14:44.874989+00:00
-- url     : https://prove2.me/theorems/ed3027fe-6dc0-404d-8bb6-3f4fb82ec3e3
-- title:
--   Qubit transpose and inverse have equal attainable sets
-- statement:
--   For every query count $k\ge0$, each of the parallel, adaptive and general classes separately has the same attainable constant coefficients for exact qubit transposition and inversion:
--
--   $$\mathcal A_c^{\rm transpose}(2,k)=\mathcal A_c^{\rm inverse}(2,k).$$
--
--   Each protocol is fixed independently of the unknown $U\in U(2)$ and implements one output channel on its success branch. The source determinant-one identity extends to all $U(2)$ at channel level because global phases cancel.
--
--   This equates two tasks within each class; it does not equate the classes.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 19, VII C

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.19, VII C: equal attainable coefficient sets for the two qubit tasks,
separately within each class. Global phases extend the SU(2) identity to U(2). -/
theorem qubit_task_equivalence (k : ℕ) (c : ProtocolClass) (p : ℝ) :
    Attainable c 2 k (targetChoi .transpose) p ↔
      Attainable c 2 k (targetChoi .inverse) p := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
