-- Prove2me | Theorems.Thm_WeightedUDNF_binary_weights_satisfiability_in_polytime
-- name    : WeightedUDNF.binary_weights_satisfiability_in_polytime
-- status  : Open
-- author  : @hao jia
-- created : 2026-10-04T11:16:26.811956+00:00
-- url     : https://prove2.me/theorems/0b8d6726-8600-4d27-b666-82e1e933e8a5
-- title:
--   Weighted satisfiability for unambiguous DNFs is in P
-- statement:
--   For every valid unambiguous DNF input with positive binary-encoded variable weights and positive binary-encoded threshold, one fixed deterministic Turing machine decides whether there is a satisfying assignment of weight at least the threshold, in time polynomial in the explicit binary input-code length. This is the weighted-satisfiability baseline recorded in the cited open-problem entry; it is not the falsifiability goal.
-- source:
--   Albertine Amarilli, “Weighted falsifiability for unambiguous DNFs,” List of open questions in theoretical computer science, section “Weighted falsifiability for unambiguous DNFs,” https://a3nm.net/work/research/questions/#weighted-falsifiability-for-unambiguous-dnfs. The entry's weighted-satisfiability paragraph.

import Definitions.Def_WeightedUDNF
import Mathlib.Computability.TuringMachine.Computable

namespace WeightedUDNF
theorem binary_weights_satisfiability_in_polytime :
    ∃ f : Input → Bool,
      ∃ machine : Turing.TM2ComputableInPolyTime encodeInput
        Computability.encodingBoolBool.encode f,
        ∀ input, validInput input → f input = satisfyingDecision input := by sorry
end WeightedUDNF
