-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_second_best_program
-- name    : SecondBestTrade.HalfEfficiency.second_best_program
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:47.625094+00:00
-- url     : https://prove2.me/theorems/be2905cc-5e91-4255-a06c-7631a926e756
-- title:
--   Lemma A.2 — Second best as a linear program
-- statement:
--   For the concrete signed-transfer Program (P), including deviations to the null report, the optimum is attained and
--   $$\mathrm{SB}=\mathrm{OPT}(P).$$
--   Every optimal feasible point $(x,p)$ of the program has an allocation rule $x$ implementable by a mechanism of the original nonnegative-transfer, reportwise balanced class, with gains from trade SB.
--
--   This preserves every optimal allocation rule, rather than merely equating two objective values.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: buyer payments and seller receipts have opposite utility signs → one signed-payment carrier with seller transfer equal to minus its receipt; reason: this is a bijective change of payment coordinates; the original mechanism still has nonnegative payments and receipts
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma A.2 — Second best as a linear program, printed p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Mechanisms

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma A.2, printed p. 19 (PDF p. 20). -/
theorem second_best_program (N : Market) :
    (∃ m : SignedMechanism N, programFeasible N m ∧ GFT N m.q = OPT N) ∧
    SB N = OPT N ∧
    (∀ m : SignedMechanism N, programFeasible N m → GFT N m.q = OPT N →
      ∃ m' : Mechanism N, admissible N m' ∧ m'.x = m.q ∧ GFT N m'.x = SB N) := by sorry

end SecondBestTrade.HalfEfficiency
