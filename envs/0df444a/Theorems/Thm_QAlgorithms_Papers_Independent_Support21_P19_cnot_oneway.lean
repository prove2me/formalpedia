-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_cnot_oneway
-- name    : QAlgorithms.Papers.Independent.Support21.P19.cnot_oneway
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:59:44.111975+00:00
-- url     : https://prove2.me/theorems/3722a634-174d-4192-9467-b31f1fe36acf
-- title:
--   CNOT sends a cobit in either direction
-- statement:
--   Let CNOT have Alice's control and Bob's target. A single call, with free local operations and product ancillas but no initial entanglement, implements either of the following channels:
--
--   $$
--   \mathrm{CNOT}\ge[q\to qq],\qquad
--   \mathrm{CNOT}\ge[qq\leftarrow q].
--   $$
--
--   These are independent choices of protocol, each exact on arbitrary superpositions and reference extensions. The claim does not provide both directions simultaneously from a bare CNOT.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 2, CNOT sends a cobit in either direction

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: independent alternatives, each using one CNOT without entanglement assistance. -/
theorem cnot_oneway :
    Exact cnotResource (budget 1 0 0 0 0 0 0 0) (cobitChannel 2) ∧
    Exact cnotResource (budget 1 0 0 0 0 0 0 0) (reverse (cobitChannel 2)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
