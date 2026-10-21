-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_superdense_coding
-- name    : QAlgorithms.Papers.Independent.Renew46.P34.superdense_coding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:09:48.435614+00:00
-- url     : https://prove2.me/theorems/d0f4fbaa-d311-4920-af87-ca575f733f62
-- title:
--   Exact super-dense coding
-- statement:
--   Alice and Bob may perform arbitrary free local quantum operations, with local ancillas, using only the resources displayed on the left. The symbol $\succeq$ means an exact finite conversion. Here $[q\to q]$ is a noiseless qubit channel, $[c\to c]$ a noiseless classical bit channel, $[qq]$ an EPR pair, and $[q\to qq]$ the isometry $|x\rangle\mapsto|x\rangle_A|x\rangle_B$ on a fixed bit basis. Quantum targets are implemented on all input operators and hence with every reference extension.
--
--   The exact conversion is
--
--   $$[q\to q]+[qq]\succeq2[c\to c].$$
--
--   One common encoder and decoder transmit every two-bit message. The target channel dephases classical data. This is background [12].
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, PDF p. 2, (SD): exact super-dense coding

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, (SD): exact classical transmission of two bits, not a coherent isometry. -/
theorem superdense_coding :
    ExactConversion emptyResource 1 1 0 (taskTarget 0 2 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P34

end
