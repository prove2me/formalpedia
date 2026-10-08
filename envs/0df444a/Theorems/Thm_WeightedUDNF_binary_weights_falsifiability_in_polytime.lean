-- Prove2me | Theorems.Thm_WeightedUDNF_binary_weights_falsifiability_in_polytime
-- name    : WeightedUDNF.binary_weights_falsifiability_in_polytime
-- status  : Open
-- author  : @hao jia
-- created : 2026-10-04T22:26:40.16304+00:00
-- url     : https://prove2.me/theorems/1d890170-ac3f-4fe6-afd3-30cbb064e229
-- title:
--   Binary-weight falsifiability for unambiguous DNFs is in P
-- statement:
--   For every valid unambiguous DNF input with positive binary-encoded variable weights and positive binary-encoded threshold, there exists one fixed deterministic Turing machine and one polynomial time bound that decide whether a falsifying assignment has total weight at least the threshold. Time is measured in the length of the explicit binary input code. This is the affirmative formal target for the open question; no proof or solution is asserted.
-- source:
--   Albertine Amarilli, “Weighted falsifiability for unambiguous DNFs,” List of open questions in theoretical computer science, section “Weighted falsifiability for unambiguous DNFs,” https://a3nm.net/work/research/questions/#weighted-falsifiability-for-unambiguous-dnfs. The entry's stated open question.

import Definitions.Def_WeightedUDNF
import Mathlib.Computability.TuringMachine.Computable

namespace WeightedUDNF
theorem binary_weights_falsifiability_in_polytime :
    ∃ f : Input → Bool,
      ∃ machine : Turing.TM2ComputableInPolyTime encodeInput
        Computability.encodingBoolBool.encode f,
        ∀ input, validInput input → f input = decision input := by sorry
end WeightedUDNF
