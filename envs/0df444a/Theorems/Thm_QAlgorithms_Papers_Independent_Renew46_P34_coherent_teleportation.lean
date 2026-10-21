-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_coherent_teleportation
-- name    : QAlgorithms.Papers.Independent.Renew46.P34.coherent_teleportation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:15:24.037995+00:00
-- url     : https://prove2.me/theorems/94ba0989-4c78-4547-bfec-b6284a7f44fa
-- title:
--   Exact coherent teleportation with EPR by-product
-- statement:
--   Alice and Bob may perform arbitrary free local quantum operations, with local ancillas, using only the resources displayed on the left. The symbol $\succeq$ means an exact finite conversion. Here $[q\to q]$ is a noiseless qubit channel, $[c\to c]$ a noiseless classical bit channel, $[qq]$ an EPR pair, and $[q\to qq]$ the isometry $|x\rangle\mapsto|x\rangle_A|x\rangle_B$ on a fixed bit basis. Quantum targets are implemented on all input operators and hence with every reference extension.
--
--   The exact conversion is
--
--   $$2[q\to qq]+[qq]\succeq[q\to q]+2[qq].$$
--
--   The input EPR pair is counted and two EPR pairs occur as separate physical output factors, jointly with the transmitted quantum state.
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, PDF p. 3, Coherent teleportation with entanglement by-product (unnumbered)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, coherent teleportation: the borrowed EPR input and both output pairs are physical. -/
theorem coherent_teleportation :
    ExactConversion (coherentResource 2) 1 0 0 (taskTarget 1 0 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P34

end
