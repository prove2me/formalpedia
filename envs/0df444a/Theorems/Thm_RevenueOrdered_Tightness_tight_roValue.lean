-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tight_roValue
-- name    : RevenueOrdered.Tightness.tight_roValue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:13.811501+00:00
-- url     : https://prove2.me/theorems/d861c22e-39d2-475d-8659-310441158584
-- title:
--   Theorem 3.4 proof, p. 10 — revenue-ordered assortments earn $(\varepsilon+\dots+\varepsilon^k)\varepsilon^{-1}<1/(1-\varepsilon)$
-- statement:
--   In the tight instance with $k\ge1$ and $0<\varepsilon\le\tfrac12$, the best of the $k$ revenue-ordered assortments is the first one, $S_1=\mathcal C$ (all products), and
--   $$
--   \mathrm{RO}=\mathrm{rev}(\mathcal C)=(\varepsilon+\varepsilon^2+\dots+\varepsilon^k)\cdot\varepsilon^{-1}<\frac{1}{1-\varepsilon}.
--   $$
--
--   The paper asserts that the first assortment is best without further detail.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, proof of Theorem 3.4

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

namespace RevenueOrdered.Tightness

/-- The revenue-ordered value of the tight instance (p. 10): the best revenue-ordered
assortment is the set of all products, whose revenue is
`(ε + ε^2 + ⋯ + ε^k) · ε^{-1} < 1/(1-ε)`. -/
theorem tight_roValue (k : ℕ) [NeZero k] (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    roValue (tightP k ε) (tightRevenue k ε) = rev (tightP k ε) (tightRevenue k ε) Finset.univ ∧
      rev (tightP k ε) (tightRevenue k ε) Finset.univ = (∑ i ∈ Finset.Icc 1 k, ε ^ i) * ε⁻¹ ∧
      (∑ i ∈ Finset.Icc 1 k, ε ^ i) * ε⁻¹ < 1 / (1 - ε) := by sorry

end RevenueOrdered.Tightness
