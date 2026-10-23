-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_G_2
-- name    : SpreadBetting.Inertial.lemma_G_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:13.742202+00:00
-- url     : https://prove2.me/theorems/eeb52c16-9c50-4fec-901e-d80bba730d44
-- title:
--   Lemma G.2, p. 50 — for 0 < r < min{2, r̄₁}: z̄ is finite iff j₁⁺(−∞) > 0, single crossing, and j₁⁺(z) > 0 for z < z̄
-- statement:
--   Let the market satisfy the standing assumptions, $\rho(z) = 1/(r_0 + rz)$ extended by (E.1), and suppose $0 < r < \min\{2, \bar r_1\}$. Write $j_1^+(z) = j_1^+(\tilde s(z)) = (2-c)\rho(z) - c/2$ and $j_1^+(-\infty) = (2-c)(\tfrac12 - \alpha) - c/2$. Let $\bar z$ be the threshold (G.1). Then:
--
--   1. (LG.2-1) If $j_1^+(-\infty) > 0$, then $\bar z$ is finite. Otherwise $\bar z = -\infty$.
--   2. (LG.2-2) (single crossing) For every $z \in \mathbb Z$,
--   $$
--   j_1^+(z)\big[\tfrac12 + \rho(z)\big] < j_1^+(z-1)\big[\tfrac12 - \rho(z)\big] \iff z \ge \bar z.
--   $$
--   3. (LG.2-3) $j_1^+(z) > 0$ for all $z < \bar z$.
--
--   The threshold $\bar z$ is the state beyond which the informed bettor stops betting; this lemma makes it well defined and single-crossing.
--
--   **Formalization Note** $j_1^+(-\infty)$ is written out as the limit of $(2-c)\rho(z) - c/2$ as $z \to -\infty$ (by (LG.1-2)). "$\bar z$ finite" is "the set of (G.1) is nonempty and bounded below", and "$\bar z = -\infty$" is "it is unbounded below"; the single-crossing clause is stated separately for the two cases (in the second it holds for every $z$).
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 50, Lemma G.2; (G.1), (G.4) p. 49; (4.7) p. 20

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_G_2 (M : Market) (hM : M.Standing) (r : ℝ) (hr : 0 < r) (hr2 : r < 2)
    (hr1 : (r : EReal) < rbar1 M) :
    let ρp := rhoIP M r
    let ρ := rhoExt M ρp
    let jPlusInf := (2 - M.c) * (1 / 2 - alpha M) - M.c / 2
    -- (LG.2-1)
    ((0 < jPlusInf → (zbarSet M ρp).Nonempty ∧ BddBelow (zbarSet M ρp)) ∧
      (jPlusInf ≤ 0 → ¬ BddBelow (zbarSet M ρp))) ∧
    -- (LG.2-2), z̄ finite
    ((zbarSet M ρp).Nonempty → BddBelow (zbarSet M ρp) → ∀ z : ℤ,
      (jPlusZ M ρp 1 z * (1 / 2 + ρ z) < jPlusZ M ρp 1 (z - 1) * (1 / 2 - ρ z) ↔ zbar M ρp ≤ z)) ∧
    -- (LG.2-2), z̄ = -∞
    (¬ BddBelow (zbarSet M ρp) → ∀ z : ℤ,
      jPlusZ M ρp 1 z * (1 / 2 + ρ z) < jPlusZ M ρp 1 (z - 1) * (1 / 2 - ρ z)) ∧
    -- (LG.2-3)
    (∀ z : ℤ, belowZbar M ρp z → 0 < jPlusZ M ρp 1 z) := by sorry

end SpreadBetting.Inertial
