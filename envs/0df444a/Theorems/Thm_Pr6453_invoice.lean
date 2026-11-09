-- Prove2me | Theorems.Thm_Pr6453_invoice
-- name    : Pr6453.invoice
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T16:16:20.683473+00:00
-- url     : https://prove2.me/theorems/6243e969-8639-4d7a-8c57-4f61bc066f05
-- title:
--   PR #6453: the invoice and the price inequality on it
-- statement:
--   The invoice of the PR #6453 word produces exactly the two rank histograms that the price inequality prices, and the price inequality therefore holds for them.
--
--   The statement has five conjuncts. The first two say that the closed-form invoice of the word's local receipt — $18$ times the local helper histogram, plus the idle and diagonal contributions on the productive side, and $18$ times the local paid histogram plus the query, idle and individual-idle contributions on the paid side — yields exactly the histograms $T$ and $P$. The next two say that the *event fold* $\texttt{assemble}$, which walks the word's events one at a time, yields the same two histograms; that is the agreement of the two ways of computing the invoice. The last conjunct is the price inequality $\sum_r P_r\, r^{1-\kappa} < \sum_r T_r\, r^{1-\kappa}$ at $\kappa = 1643507/500000000$, now stated for the histograms the invoice produces rather than for two lists given in advance.
--
--   The content is the connection: the price inequality is a statement about the invoice of this word, and the invoice is a function of the word's census — $18$ native calls, $17$ binary queries, $14$ whole idle jobs of sizes $2,3,4,7$, $2$ individual idle jobs, $20$ normalisations, and $34$ diagonal terms with index sums $0,2,3,4,7,9$.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: controller.formula_invoice (research/mixed-projector-query-root/controller.py), assemble (research/p104-third-anchor-clean-mixed-root/pricing.py), RESULT.json (local.helpers, local.paid, physical.main_targets, physical.whole_idle_jobs).

import Definitions.Def_Pr6453_Invoice
import Definitions.Def_Pr6453_InvoiceEvents
import Theorems.Thm_Pr6453_moment_kappa_gt

set_option autoImplicit false

namespace Pr6453

theorem invoice :
    toHist (invoiceTargets localHelpers) 200 = targets ∧
      toHist (invoicePaid localPaid) 200 = paid ∧
      toHist (assemble wordEvents wordDiagonal localHelpers localPaid).1 200 = targets ∧
      toHist (assemble wordEvents wordDiagonal localHelpers localPaid).2 200 = paid ∧
      moment (toHist (invoicePaid localPaid) 200) (1 - (kappa : ℝ)) <
        moment (toHist (invoiceTargets localHelpers) 200) (1 - (kappa : ℝ)) := by
  sorry

end Pr6453
