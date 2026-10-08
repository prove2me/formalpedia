-- Prove2me | Theorems.Thm_WeightedUDNF_unary_weights_falsifiability_in_polytime
-- name    : WeightedUDNF.unary_weights_falsifiability_in_polytime
-- status  : Open
-- author  : @hao jia
-- created : 2026-10-04T12:36:13.726486+00:00
-- url     : https://prove2.me/theorems/f1b27a64-33b2-427b-a253-e363327d768a
-- title:
--   Unary-weight falsifiability for unambiguous DNFs is in P
-- statement:
--   For every valid unambiguous DNF input whose positive variable weights are encoded in unary and whose positive threshold remains binary-encoded, one fixed deterministic Turing machine decides whether some falsifying assignment has weight at least the threshold, in time polynomial in the explicit code length. This is the unary-weight partial result recorded in the cited source entry.
-- source:
--   Albertine Amarilli, “Weighted falsifiability for unambiguous DNFs,” List of open questions in theoretical computer science, section “Weighted falsifiability for unambiguous DNFs,” https://a3nm.net/work/research/questions/#weighted-falsifiability-for-unambiguous-dnfs. The entry's partial notes on unary weights.

import Definitions.Def_WeightedUDNF
import Mathlib.Computability.TuringMachine.Computable

namespace WeightedUDNF
theorem unary_weights_falsifiability_in_polytime :
    ∃ f : Input → Bool,
      ∃ machine : Turing.TM2ComputableInPolyTime encodeInputUnaryWeights
        Computability.encodingBoolBool.encode f,
        ∀ input, validInput input → f input = decision input := by sorry
end WeightedUDNF
