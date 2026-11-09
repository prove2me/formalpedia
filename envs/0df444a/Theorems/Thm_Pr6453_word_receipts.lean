-- Prove2me | Theorems.Thm_Pr6453_word_receipts
-- name    : Pr6453.word_receipts
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T18:20:39.711694+00:00
-- url     : https://prove2.me/theorems/b22d132f-6412-478c-86eb-76201f168cc2
-- title:
--   PR #6453: the receipts of the word
-- statement:
--   The receipts of the PR #6453 word, at the numbers `WORD.json` and `RESULT.json` print.
--
--   The program of the word has 17 926 events across the five tags; the native development supplies 562 helpers, distributed over ranks 1 to 9 as 14, 8, 4, 107, 15, 3, 9, 39 and 363; the native receipt counts 2 941 distinct maps, 1 124 helper normalizers and 208 main adapters; and the physical receipt counts 799 columns, 7 488 physical contacts, 53 248 central square columns, 18 full calls and 104 ports.
--
--   These are the numbers a formalisation of the construction has to reproduce: the event total fixes the length of the program, the helper histogram fixes the rank support of the invoice, and the distinct-map count is the size of the object the native development has to provide.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: WORD.json (census of the program) and RESULT.json (native.helpers, native.distinct_maps, physical.columns).

import Definitions.Def_Pr6453_Word

set_option autoImplicit false

namespace Pr6453

theorem word_receipts :
    (census.map (fun p => p.2)).sum = 17926 ∧
      (helperHistogram.map (fun p => p.2)).sum = 562 ∧
      nativeReceipt.1 = 2941 ∧ physicalReceipt.1 = 799 := by
  sorry

end Pr6453
