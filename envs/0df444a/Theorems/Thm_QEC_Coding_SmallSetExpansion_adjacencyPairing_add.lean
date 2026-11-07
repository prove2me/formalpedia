-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_adjacencyPairing_add
-- name    : QEC.Coding.SmallSetExpansion.adjacencyPairing_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:35:37.295371+00:00
-- url     : https://prove2.me/theorems/50f05e2e-d460-492e-859c-a6a243530288
-- title:
--   Small Set Expansion: adjacency Pairing add
-- statement:
--   The Small Set Expansion construction uses the adjacency Pairing add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionOperators.lean#L33-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansionOperators.lean#L33-L36

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V]

theorem QEC.Coding.SmallSetExpansion.adjacencyPairing_add (M N : WeightedGraph V) (f g : V → ℝ) :
    adjacencyPairing (add M N) f g = adjacencyPairing M f g + adjacencyPairing N f g := by sorry
