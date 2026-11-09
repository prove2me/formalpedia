-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_useful_duals
-- name    : SecondBestTrade.HalfEfficiency.useful_duals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:17.488644+00:00
-- url     : https://prove2.me/theorems/32d6c5ab-c64e-4cc5-90fe-216529a27537
-- title:
--   Lemma A.7 — Useful duals
-- statement:
--   For a nonnegative multiplier vector $z$, the supremum of (A.5) over feasible allocations and free signed transfers is finite exactly when the flow conservation equations make $z$ useful:
--   $$\bigl(\exists r\in\mathbb R:L^*(z)=r\bigr)\quad\Longleftrightarrow\quad z\text{ is useful}.$$
--   If $z$ is not useful then $L^*(z)=+\infty$.
--
--   Thus non-useful multipliers are represented by a genuinely infinite dual value, preserving the unrestricted transfer directions.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: buyer payments and seller receipts have opposite utility signs → one signed-payment carrier with seller transfer equal to minus its receipt; reason: this is a bijective change of payment coordinates; the original mechanism still has nonnegative payments and receipts
--   - encoding: finite value or positive infinity → existence of a real value in EReal, and top in the non-useful case; reason: this preserves both alternatives without the default value of an unbounded real supremum
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Lemma A.7 — Useful duals, printed p. 23 (PDF p. 24)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Lagrangian

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Lemma A.7, printed p. 23 (PDF p. 24). -/
theorem useful_duals (N : Market) (z : Dual N) :
    ((∃ r : ℝ, lagrangianSup N z = (r : EReal)) ↔ useful N z) ∧
    (¬ useful N z → lagrangianSup N z = ⊤) := by sorry

end SecondBestTrade.HalfEfficiency
