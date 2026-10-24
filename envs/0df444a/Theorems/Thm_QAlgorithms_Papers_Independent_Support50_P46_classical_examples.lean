-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P46_classical_examples
-- name    : QAlgorithms.Papers.Independent.Support50.P46.classical_examples
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T23:57:02.471159+00:00
-- url     : https://prove2.me/theorems/984a8a72-40a6-4166-9113-9f2b1ba6d31a
-- title:
--   Two classical three-qubit states have opposite tripartite information
-- statement:
--   Let A, B and C be qubits, in that order, and let
--
--   $$
--   \rho=\tfrac12(|000\rangle\langle000|+|111\rangle\langle111|),\qquad
--   \tau=\tfrac14(|000\rangle\langle000|+|011\rangle\langle011|+|101\rangle\langle101|+|110\rangle\langle110|).
--   $$
--
--   Both matrices are normalized density operators. With S the von Neumann entropy in bits of the actual reduced state, define I₃(A:B:C)=S(A)+S(B)+S(C)−S(AB)−S(AC)−S(BC)+S(ABC). Then
--
--   $$
--   I_3(A:B:C)_\rho=1,\qquad I_3(A:B:C)_\tau=-1.
--   $$
--
--   These explicit classical correlations exhibit both signs and disprove general mutual-information monogamy.
-- source:
--   Holographic Mutual Information is Monogamous, arXiv:1107.2940v2, PDF p. 5, §2, (2.1)–(2.2): classical positive and negative I3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P46

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Gap48.P20 (subsystemEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.5, (2.1)–(2.2): both signs occur for the two displayed classical
states, with entropy in bits and actual reduced density matrices. -/
theorem classical_examples :
    IsDensityMatrix redundantClassical ∧ IsDensityMatrix xorClassical ∧
    tripartiteInformation redundantClassical {0} {1} {2} = 1 ∧
    tripartiteInformation xorClassical {0} {1} {2} = -1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P46

end
