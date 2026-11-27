-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_Supplement_lemma_4
-- name    : SPPRevenue.SingleUnit.Supplement.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:15:33.554887+00:00
-- url     : https://prove2.me/theorems/4e88d9ea-e15d-4614-83f1-fd42a96cffac
-- title:
--   Lemma 4 — for H > 1 the cutoff τ⋆ > 1/H is unique and FR-Multi(H) = 1 + ln(Hτ⋆)
-- statement:
--   Let $H>1$ be an integer. The equation
--   $$\int_{1/H}^{\tau^\star}\Big(H-e^{-1/\tau}\sum_{i=0}^{H-1}\frac{H-i}{\tau^i\,i!}\Big)\,d\tau=\frac{H^H}{H!\,e^H}$$
--   has exactly one solution $\tau^\star>1/H$. For it, the program (FR-Multi(H)) attains its maximum, which is positive and finite, and
--   $$\mathrm{FR\text{-}Multi}(H)=1+\ln(H\tau^\star).$$
--
--   This closed form is what shows that $1/\mathrm{FR\text{-}Multi}(H)$ beats the earlier bound $1-H^H/(H!e^H)$ in Theorem 3.
--
--   **Formalization Note** (FR-Multi(H)) is the program of Theorem 3 with $s\le\min(H,1/\tau)$ written as $s\le H$ and $\tau s\le1$.
--
--   Differences from the source:
--   - reading: let τ⋆ > 1/H be the unique solution … then FR-Multi(H) is given by 1 + ln(Hτ⋆) → existence and uniqueness (∃!) of the root T > 1/H, and for every such root: the program is attained, positive and finite and frMulti H = 1 + log(H·T); reason: the source presupposes the root and the max; both are stated as conclusions
--   - encoding: 0 ≤ s(τ) ≤ min(H, 1/τ) → 0 ≤ s τ ∧ s τ ≤ H ∧ τ * s τ ≤ 1; reason: the same constraint at every τ ≥ 0, avoiding 1/0 = 0
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 20, Lemma 4; proof §8.5, p. 38

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiProgram

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem lemma_4 (H : ℕ) (hH : 1 < H) :
    (∃! T : ℝ, 1 / (H : ℝ) < T ∧ multiRootEq H T) ∧
      ∀ T : ℝ, 1 / (H : ℝ) < T → multiRootEq H T →
        IsFactorProgram (frMultiValues H) ∧
          frMulti H = ENNReal.ofReal (1 + Real.log ((H : ℝ) * T)) := by sorry

end SPPRevenue.SingleUnit.Supplement
