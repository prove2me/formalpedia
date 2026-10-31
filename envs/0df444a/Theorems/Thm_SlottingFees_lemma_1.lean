-- Prove2me | Theorems.Thm_SlottingFees_lemma_1
-- name    : SlottingFees.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:30.701+00:00
-- url     : https://prove2.me/theorems/a97ba901-2680-4545-8646-2d3764af9757
-- title:
--   Lemma 1 — stage-3 pricing $(q_i+w_i)/2$ and assortment when $|A|=1$ (corrected: $w_i\le q_i$)
-- statement:
--   Consider the low-variety subgame, under the standing assumptions $q_1>q_2$ and $q_l>c_l\ge0$. Let $i\in\{1,2\}$ and $j\neq i$.
--
--   1. For a wholesale price $0\le w_i\le q_i$, the retailer's pricing problem (4) for $A=\{i\}$ has the unique solution
--   $$
--   \tilde p_i(w_i)=\frac{q_i+w_i}{2},
--   $$
--   with optimal gross profit $(q_i-w_i)^2/(4q_i)$.
--   2. If manufacturer $i$ participates and manufacturer $j$ does not, the retailer sets $A=\{i\}$.
--   3. If both participate, with wholesale prices $w_l\ge 0$ for $l=1,2$, then $\{i\}$ is an optimal assortment for the retailer if
--   $$
--   w_i\le q_i-(q_j-w_j)\sqrt{q_i/q_j};
--   $$
--   when moreover $w_l\le q_l$ for $l=1,2$, the converse holds as well.
--
--   The threshold in part 3 is the retailer's incentive-compatibility constraint (7) that the entrant of the $|A|=1$ subgame must respect.
--
--   Differences from the source:
--   - correction: p̃_i(w_i) = (q_i + w_i)/2 for every w_i → for 0 ≤ w_i ≤ q_i; reason: for q_i = 1, w_i = 2 the point 1.5 lies outside [0, q_i] and the maximizer of (4) is q_i
--   - reading: 'the retailer sets A = {i} if w_i ≤ q_i − (q_j − w_j)√(q_i/q_j)' → {i} is an optimal stage-3 assortment; reason: at equality both single-product assortments give the retailer the same profit
--   - generalization: if → if, and also only if when 0 ≤ w_l ≤ q_l for l = 1, 2; reason: the converse also holds there; the 'if' direction, the source's claim, is stated for all w_l ≥ 0
--   - generalization: wholesale prices w_l ≥ c_l → w_l ≥ 0 (parts 1 and 3); reason: c_l ≥ 0, so every price the model allows is covered
--   - encoding: retail-price problems (4) and (12) include the constants S − K and 2S − 2K → the optimal-price predicates maximize the gross profit only; reason: adding a constant does not change the maximizers
--   - encoding: products 1 and 2; Pr over θ ~ U[0,1] → indices 0 and 1 of Fin 2; Lebesgue measure of the set of types in [0,1], as a real number; reason: Lean convention; same instances
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Lemma 1, p.10

import Mathlib
import Definitions.Def_SlottingFees_Subgame1

namespace SlottingFees

/-- **Lemma 1**, p.10 (Alan, Kurtuluş, Nakkas, *Retail Category Management with Slotting Fees*,
MSOM 2024, doi:10.1287/msom.2022.0143): stage-3 pricing and assortment when `|A| = 1`.

Under the standing assumptions (`q₁ > q₂`, `q_l > c_l ≥ 0`), for `i ∈ {1, 2}` and `j ≠ i`:

* (a) for `0 ≤ w_i ≤ q_i`, the unique solution of (4) is `p̃_i(w_i) = (q_i + w_i)/2`, with
  optimal gross profit `(q_i − w_i)²/(4q_i)`;
* (b) if only manufacturer `i` participates, the retailer sets `A = {i}`;
* (c) if both participate (wholesale prices `w_l ≥ 0`), `{i}` is an optimal assortment if
  `w_i ≤ q_i − (q_j − w_j)√(q_i/q_j)`; for `0 ≤ w_l ≤ q_l` the converse holds as well.

**Formalization Note** The bound `w_i ≤ q_i` is added in (a) (correction): for `w_i > q_i` the
price `(q_i + w_i)/2` lies outside `[0, q_i]`. The printed "if" of (c) is stated for all
`w_l ≥ 0` (which covers the model's `w_l ≥ c_l ≥ 0`); only the added converse needs
`w_l ≤ q_l`. The gross profit in (a) is the paper's
`Π̃_r^{{i}}(w_i) − S + K` (p.11). In (c) "the retailer sets `A = {i}` if …" is stated as an
equivalence about optimality: at equality both assortments are optimal. Product 1 is `0`. -/
theorem lemma_1 (ω : Params) (hω : ω.Standing) (i : Fin 2) :
    (∀ w : ℝ, 0 ≤ w → w ≤ ω.q i →
      (∀ p : ℝ, IsOptPrice1 ω i w p ↔ p = (ω.q i + w) / 2) ∧
      optGross1 ω i w = (ω.q i - w) ^ 2 / (4 * ω.q i)) ∧
    (∀ (w : Fin 2 → ℝ) (k : Fin 2), IsOptAssortment1 ω {i} w k ↔ k = i) ∧
    (∀ w : Fin 2 → ℝ, (∀ l, 0 ≤ w l) →
      w i ≤ ω.q i - (ω.q (other i) - w (other i)) * Real.sqrt (ω.q i / ω.q (other i)) →
      IsOptAssortment1 ω Finset.univ w i) ∧
    (∀ w : Fin 2 → ℝ, (∀ l, 0 ≤ w l ∧ w l ≤ ω.q l) →
      (IsOptAssortment1 ω Finset.univ w i ↔
        w i ≤ ω.q i - (ω.q (other i) - w (other i)) * Real.sqrt (ω.q i / ω.q (other i)))) := by sorry

end SlottingFees
