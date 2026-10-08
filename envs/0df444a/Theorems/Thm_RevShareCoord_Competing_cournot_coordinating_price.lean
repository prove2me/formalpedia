-- Prove2me | Theorems.Thm_RevShareCoord_Competing_cournot_coordinating_price
-- name    : RevShareCoord.Competing.cournot_coordinating_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T00:53:15.962209+00:00
-- url     : https://prove2.me/theorems/b8ba29ea-f452-4811-8145-d2b45d18e86e
-- title:
--   Sec. 4.1.2 — Cournot: q_i^I = (1 − c)/(2 + 2β(n − 1)), R_j^i = −βq_j, and the coordinating price w^I
-- statement:
--   Let $n$ retailers have the Cournot revenues $R_i(\bar q) = q_i(1 - q_i - \beta\sum_{j\ne i} q_j)$ with $0\le\beta<1$, and let the unit cost satisfy $0 < c < 1$. Then:
--
--   1. the integrated channel stocks the symmetric profile
--   $$q_i^I = \frac{1-c}{2+2\beta(n-1)},$$
--   which maximizes the system profit $\Pi(\bar q) = \sum_i R_i(\bar q) - c\sum_i q_i$ over $\bar q \ge 0$ and is its only maximizer there;
--   2. $R_j^i(\bar q) = \partial R_j/\partial q_i(\bar q) = -\beta q_j$ for all $j \ne i$;
--   3. consequently the coordinating price $c - \sum_{j\ne i} R_j^i(\bar q^I)$ is the same for every retailer and equals
--   $$w^I = c + \frac{\beta(n-1)(1-c)}{2+2\beta(n-1)};$$
--   4. at the common wholesale price $w^I$ (no revenue sharing), $\bar q^I$ is a Nash equilibrium of the retailers' game, so the system is coordinated.
--
--   **Formalization Note** The page leaves $c < 1$ implicit; it is needed for a positive integrated quantity.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 19 (PDF p. 20), Section 4.1.2, second paragraph and display of w^I

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 4.1.2, the integrated quantities and the coordinating price (p. 19).** Cournot
revenues (7), `Rᵢ(q̄) = qᵢ(1 − qᵢ − β Σ_{j≠i} qⱼ)`, with `0 ≤ β < 1` and unit cost `0 < c < 1`.
1. The symmetric profile `q_i^I = (1 − c)/(2 + 2β(n − 1))` maximizes the system profit
   `Π(q̄) = Σᵢ Rᵢ(q̄) − c Σᵢ qᵢ` over `q̄ ≥ 0`, and is its only maximizer there.
2. `R_j^i(q̄) = ∂R_j/∂q_i (q̄) = −β q_j` for all `j ≠ i` and every profile `q̄`.
3. The coordinating price `c − Σ_{j≠i} R_j^i(q̄^I)` equals
   `w^I = c + β(n − 1)(1 − c)/(2 + 2β(n − 1))` for every `i`.
4. At the common wholesale price `w^I` (no revenue sharing) the profile `q̄^I` is a Nash
   equilibrium. -/
theorem cournot_coordinating_price {n : ℕ} (β c : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc0 : 0 < c) (hc1 : c < 1) :
    (IsMaxOn (systemProfit (cournotRevenue β) c) {q : Fin n → ℝ | ∀ i, 0 ≤ q i}
        (fun _ => cournotQI β n c) ∧
      ∀ q ∈ {q : Fin n → ℝ | ∀ i, 0 ≤ q i},
        IsMaxOn (systemProfit (cournotRevenue β) c) {q : Fin n → ℝ | ∀ i, 0 ≤ q i} q →
          q = fun _ => cournotQI β n c) ∧
    (∀ (q : Fin n → ℝ) (i j : Fin n), j ≠ i →
      HasDerivAt (fun t => cournotRevenue β j (Function.update q i t)) (-β * q j) (q i)) ∧
    (∀ i : Fin n, c - ∑ j ∈ univ.erase i, (-β * cournotQI β n c) = cournotWI β n c) ∧
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => cournotWI β n c)
      (fun _ => cournotQI β n c) := by sorry

end RevShareCoord.Competing
