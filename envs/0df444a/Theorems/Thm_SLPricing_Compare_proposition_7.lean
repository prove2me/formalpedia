-- Prove2me | Theorems.Thm_SLPricing_Compare_proposition_7
-- name    : SLPricing.Compare.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:55.966523+00:00
-- url     : https://prove2.me/theorems/326d74cd-97af-4731-b381-179c656576c4
-- title:
--   Proposition 7, p. 24 — without SL, pre-announced pricing earns at least as much as responsive pricing, with gap $\delta_c^2(1-c)^2(1-\delta_c)/(4(9-2\delta_c^2-3\delta_c))$
-- statement:
--   In the absence of SL ($\gamma = 0$), let $\pi^*_{bp}$ and $\pi^*_{br}$ be the firm's optimal expected profits under pre-announced and responsive pricing. Both are finite, and
--   $$\Delta\pi^*_b = \pi^*_{bp} - \pi^*_{br} = \frac{\delta_c^2(1-c)^2(1-\delta_c)}{4\,(9 - 2\delta_c^2 - 3\delta_c)} .$$
--   In particular $\Delta\pi^*_b \ge 0$ for every $\delta_c \in [0,1]$, and $\pi^*_{br} < \pi^*_{bp}$ strictly when $0 < \delta_c < 1$.
--
--   This is the benchmark that Proposition 8 contrasts with: without learning, commitment is (weakly) valuable for the firm, as in the earlier literature on strategic consumers.
--
--   **Formalization Note** "Higher" is read as the proof states it: the gap is non-negative on $[0,1]$ and strictly positive on $(0,1)$; at $\delta_c \in \{0,1\}$ the two values coincide. The denominator is at least $4$ on $[0,1]$.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Proposition 7, p. 24; proof in Appendix A, p. 33

import Mathlib
import Definitions.Def_SLPricing_Compare_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Compare

/-- Proposition 7, p. 24 (proof p. 33): in the absence of SL (`γ = 0`), the optimal expected
profits are finite and differ by `Δπ*_b = π*_bp − π*_br = δc²(1−c)²(1−δc)/(4(9 − 2δc² − 3δc)) ≥ 0`;
the difference is strictly positive for `δc ∈ (0, 1)`. -/
theorem proposition_7 (P : Params) (hP : P.Standing) :
    (∃ v : ℝ, respValue P.noSL = (v : EReal) ∧
      preValue P.noSL = ((v + P.δc ^ 2 * (1 - P.c) ^ 2 * (1 - P.δc) /
        (4 * (9 - 2 * P.δc ^ 2 - 3 * P.δc)) : ℝ) : EReal)) ∧
    (0 < P.δc → P.δc < 1 → respValue P.noSL < preValue P.noSL) := by sorry

end SLPricing.Compare
