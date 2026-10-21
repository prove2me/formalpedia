-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_catalytic_coherent_bit_equivalence
-- name    : QAlgorithms.Papers.Independent.Renew46.P34.catalytic_coherent_bit_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:16:15.400258+00:00
-- url     : https://prove2.me/theorems/15c647bb-66dc-489f-b52d-eeff640e8b71
-- title:
--   Finite catalytic coherent-bit equivalence
-- statement:
--   Alice and Bob may perform arbitrary free local quantum operations, with local ancillas, using only the resources displayed on the left. The symbol $\succeq$ means an exact finite conversion. Here $[q\to q]$ is a noiseless qubit channel, $[c\to c]$ a noiseless classical bit channel, $[qq]$ an EPR pair, and $[q\to qq]$ the isometry $|x\rangle\mapsto|x\rangle_A|x\rangle_B$ on a fixed bit basis. Quantum targets are implemented on all input operators and hence with every reference extension.
--
--   Borrowing and exactly returning one EPR pair permits the equivalence
--
--   $$2[q\to qq]\equiv^{c}[q\to q]+[qq].$$
--
--   Precisely, two coherent bits and one input EPR pair yield one transmitted qubit and two output EPR pairs; in the reverse direction one qubit channel and two input EPR pairs yield two coherent bits and one returned EPR pair. The catalyst is an explicit output factor, so it is returned independently of the quantum task. This finite statement is distinct from asymptotic recycling.
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, PDF p. 3, Catalytic coherent-bit equivalence (unnumbered)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, finite catalytic equivalence. Each direction borrows exactly one EPR pair:
2 cobits plus the catalyst yield one qubit and two EPR pairs; one qubit and two input
EPR pairs yield 2 cobits and the returned EPR catalyst. -/
theorem catalytic_coherent_bit_equivalence :
    ExactConversion (coherentResource 2) 1 0 0 (taskTarget 1 0 2) ∧
    ExactConversion emptyResource 2 1 0 (coherentTarget 2 1) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P34

end
