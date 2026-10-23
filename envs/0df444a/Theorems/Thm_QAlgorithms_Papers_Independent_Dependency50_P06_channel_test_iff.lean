-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_channel_test_iff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.channel_test_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:22:20.569711+00:00
-- url     : https://prove2.me/theorems/441826db-67bf-485c-80e2-638bdf9b9423
-- title:
--   Under CPP it suffices to test channel inputs
-- statement:
--   All quantum systems below have finite, nonzero dimension, with fixed orthonormal bases; one-dimensional systems are allowed. A channel system $A=(A_0,A_1)$ consists of an input and an output system, and likewise for $B$. A map is complex-linear on its full operator space. Density matrices are positive semidefinite with trace one. Let $\Theta:A\to B$ be CPP. Then
--
--   $$[\forall E\text{ CPTNI},\;\Theta[E]\text{ is CPTNI}]\quad\Longleftrightarrow\quad[\forall N\text{ CPTP},\;\Theta[N]\text{ is CPTNI}].$$
--
--   Equivalently, the trace bound is tested on every density matrix at the output-map input. This reduces verification of CPTNI preservation to normalized input channels.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 9, Appendix A, after (A.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section QuantumResults

variable {A0 A1 B0 B1 : Type}

variable [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]

variable [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]

/-- PDF pp.2,9, Appendix A: under CPP, testing channels is equivalent to
testing every CPTNI input. CPTNI-map completion is not a hypothesis. -/
theorem channel_test_iff (S : Supermap A0 A1 B0 B1) (hS : IsCPP S) :
    (∀ E : QMap A0 A1, IsCPTNI E → IsCPTNI (superApply S E)) ↔
      (∀ N : QMap A0 A1, IsChannel N → IsCPTNI (superApply S N)) := by sorry

end QuantumResults

end QAlgorithms.Papers.Independent.Dependency50.P06

end
