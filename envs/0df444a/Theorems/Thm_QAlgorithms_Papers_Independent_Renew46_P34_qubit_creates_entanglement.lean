-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_qubit_creates_entanglement
-- name    : QAlgorithms.Papers.Independent.Renew46.P34.qubit_creates_entanglement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:10:24.573399+00:00
-- url     : https://prove2.me/theorems/4f832c08-bc43-4e3a-be2d-5403a4b738c6
-- title:
--   A qubit channel creates an EPR pair
-- statement:
--   Alice and Bob may perform arbitrary free local quantum operations, with local ancillas, using only the resources displayed on the left. The symbol $\succeq$ means an exact finite conversion. Here $[q\to q]$ is a noiseless qubit channel, $[c\to c]$ a noiseless classical bit channel, $[qq]$ an EPR pair, and $[q\to qq]$ the isometry $|x\rangle\mapsto|x\rangle_A|x\rangle_B$ on a fixed bit basis. Quantum targets are implemented on all input operators and hence with every reference extension.
--
--   The exact conversion is
--
--   $$[q\to q]\succeq[qq].$$
--
--   Sending one locally prepared EPR half creates one shared EPR pair; the statement is a conversion in the displayed direction.
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, PDF p. 2, (QE): qubit channel creates entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, (QE): send half of a locally prepared EPR pair using one qubit channel. -/
theorem qubit_creates_entanglement :
    ExactConversion emptyResource 0 1 0 (taskTarget 0 0 1) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P34

end
