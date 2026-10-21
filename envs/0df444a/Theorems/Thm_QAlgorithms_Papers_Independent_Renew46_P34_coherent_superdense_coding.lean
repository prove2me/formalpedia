-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_coherent_superdense_coding
-- name    : QAlgorithms.Papers.Independent.Renew46.P34.coherent_superdense_coding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:14:32.783426+00:00
-- url     : https://prove2.me/theorems/4ea92a20-f791-4522-8d69-4be1101ce944
-- title:
--   Exact coherent super-dense coding
-- statement:
--   Alice and Bob may perform arbitrary free local quantum operations, with local ancillas, using only the resources displayed on the left. The symbol $\succeq$ means an exact finite conversion. Here $[q\to q]$ is a noiseless qubit channel, $[c\to c]$ a noiseless classical bit channel, $[qq]$ an EPR pair, and $[q\to qq]$ the isometry $|x\rangle\mapsto|x\rangle_A|x\rangle_B$ on a fixed bit basis. Quantum targets are implemented on all input operators and hence with every reference extension.
--
--   The exact conversion is
--
--   $$[q\to q]+[qq]\succeq2[q\to qq].$$
--
--   The target retains off-diagonal coherences. This result is attributed to Harrow [16].
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, PDF p. 3, Coherent super-dense coding (unnumbered)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, coherent super-dense coding, attributed there to Harrow [16]. -/
theorem coherent_superdense_coding :
    ExactConversion emptyResource 1 1 0 (coherentResource 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P34

end
