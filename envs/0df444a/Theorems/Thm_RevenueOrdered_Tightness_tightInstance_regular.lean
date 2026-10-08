-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tightInstance_regular
-- name    : RevenueOrdered.Tightness.tightInstance_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:11.508145+00:00
-- url     : https://prove2.me/theorems/b1a430c2-c14d-4dfe-8e14-f32800f8115a
-- title:
--   Theorem 3.4 proof, p. 10 — the tight instance is a regular discrete choice model
-- statement:
--   For every $k$ and every $0<\varepsilon\le\tfrac12$, the system of choice probabilities $\mathcal P$ of the tight instance satisfies the axioms (i)–(iv) of a regular discrete choice model:
--   $$
--   \mathcal P\ \text{is regular.}
--   $$
--
--   The paper deduces this from (i), (ii) (stated as clear), the bound for (iii), and (7) and (9).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, proof of Theorem 3.4 ("We deduce from (7) and (9) …")

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

namespace RevenueOrdered.Tightness

/-- The constructed system of choice probabilities is a regular discrete choice model
(p. 10): axioms (i)–(iv). -/
theorem tightInstance_regular (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    IsRegular (tightP k ε) := by sorry

end RevenueOrdered.Tightness
