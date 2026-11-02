-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_BinaryAdder_Normalizer_normalizeOutput_exec
-- name    : TwoAgentSched.TotalTotal.BinaryAdder.Normalizer.normalizeOutput_exec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T22:37:38.391976+00:00
-- url     : https://prove2.me/theorems/1ae3504b-7d36-48dc-8ddf-47be88a413c6
-- title:
--   Exact stack execution of binary-adder normalization
-- statement:
--   For arbitrary output and carry-history stacks, the fixed normalizer removes the maximal leading zero prefix of the output, reverses the remaining symbols onto the first stack, clears the output and carry history, and resets the carry to zero. Its exact cost is three times the length of each of the discarded prefix, remaining output and carry history, plus seven structured-program steps.

import Definitions.Def_TwoAgentSched_TotalTotal_BinaryAdderNormalizer
open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.TotalTotal.BinaryAdder

namespace TwoAgentSched.TotalTotal.BinaryAdder.Normalizer
theorem normalizeOutput_exec (output carries : List BSym) :
    normalizeOutput.Exec (store [] [] output carries)
      (store (output.dropWhile (fun x => x == BSym.zero)).reverse [] [] [.zero])
      (3 * (output.takeWhile (fun x => x == BSym.zero)).length +
       3 * (output.dropWhile (fun x => x == BSym.zero)).length + 3 * carries.length + 7) := by
  sorry

end TwoAgentSched.TotalTotal.BinaryAdder.Normalizer
