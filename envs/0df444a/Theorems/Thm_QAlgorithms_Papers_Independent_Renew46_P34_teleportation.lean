-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P34_teleportation
-- name    : QAlgorithms.Papers.Independent.Renew46.P34.teleportation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:08:56.466679+00:00
-- url     : https://prove2.me/theorems/99c6ed6e-302f-407f-b883-de3abf5f9906
-- title:
--   Exact teleportation
-- statement:
--   Alice and Bob may perform arbitrary free local quantum operations, with local ancillas, using only the resources displayed on the left. The symbol $\succeq$ means an exact finite conversion. Here $[q\to q]$ is a noiseless qubit channel, $[c\to c]$ a noiseless classical bit channel, $[qq]$ an EPR pair, and $[q\to qq]$ the isometry $|x\rangle\mapsto|x\rangle_A|x\rangle_B$ on a fixed bit basis. Quantum targets are implemented on all input operators and hence with every reference extension.
--
--   The exact conversion is
--
--   $$2[c\to c]+[qq]\succeq[q\to q].$$
--
--   This is the exact teleportation conversion cited as background [11].
-- source:
--   A family of quantum protocols, arXiv:quant-ph/0308044v2, PDF p. 2, (TP): exact teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P34

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P34

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, (TP): exact teleportation, two classical bits and one EPR pair per qubit. -/
theorem teleportation :
    ExactConversion emptyResource 1 0 2 (taskTarget 1 0 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P34

end
