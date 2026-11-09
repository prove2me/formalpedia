-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_finite_linear_program
-- name    : SecondBestTrade.HalfEfficiency.finite_linear_program
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:35.902963+00:00
-- url     : https://prove2.me/theorems/1a4ff534-3c33-4f39-8dca-85c2e374cd7c
-- title:
--   Lemma A.6 — Finite linear program
-- statement:
--   For the finite market, Program (P) has finitely many allocation and transfer variables and a finite linear-inequality presentation with linear objective. The number of variables is $(|E|+|I|+|J|)|T_I\times T_J|$. Moreover,
--   $$0\text{ is feasible},\qquad \mathrm{GFT}(x)\le\mathrm{FB}\text{ for every feasible point},\qquad\exists(x,p)\text{ feasible}:\mathrm{GFT}(x)=\mathrm{OPT}(P).$$
--   In particular the optimum is attained even though signed transfers need not be bounded. The finite inequality presentation and attainment are conclusions, rather than market assumptions.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: buyer payments and seller receipts have opposite utility signs → one signed-payment carrier with seller transfer equal to minus its receipt; reason: this is a bijective change of payment coordinates; the original mechanism still has nonnegative payments and receipts
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma A.6 — Finite linear program, printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Mechanisms

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma A.6, printed p. 21 (PDF p. 22). -/
theorem finite_linear_program (N : Market) :
    finiteLPPresentation N ∧
    Fintype.card (Variable N) = (N.ne + N.nb + N.ns) * Fintype.card (Profile N) ∧
    programFeasible N (zeroSigned N) ∧
    (∀ m : SignedMechanism N, programFeasible N m → GFT N m.q ≤ FB N) ∧
    ∃ m : SignedMechanism N, programFeasible N m ∧ GFT N m.q = OPT N := by sorry

end SecondBestTrade.HalfEfficiency
