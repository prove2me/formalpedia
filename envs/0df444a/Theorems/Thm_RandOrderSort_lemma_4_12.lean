-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_12
-- name    : RandOrderSort.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:56.384009+00:00
-- url     : https://prove2.me/theorems/ce123016-a2c0-4b35-afad-b0906705b242
-- title:
--   Lemma 4.12 — arrival and next-reallocation tails
-- statement:
--   Let $n\ge 8192$, $q\in(0,1)$ and $1\le i<k$, and condition on $P_L$. A good selected parent $J_{q,2^is}$ with $2s$ current buckets in phase $i$ satisfies
--   $$\mathbb P\bigl(\exists\text{ child }I\text{ of }J_{q,2^is}:N_i(I)>Bs\bigm|P_L\bigr)\le 2e^{-Bs/200}.$$
--   If $i+1<k$, a good selected parent $J_{q,2^{i+1}s}$ with $2s$ current buckets in phase $i+1$ satisfies
--   $$\mathbb P\bigl(\exists\text{ child }I\text{ of }J_{q,2^{i+1}s}:N_i(I)<1.1Bs\bigm|P_L\bigr)\le 2e^{-Bs/65}.$$
--   Each event contains the corresponding local overflow event, for current arrivals and the following reallocation, respectively.
--
--   The same arrival count therefore controls both overflow mechanisms: too many arrivals in a current interval, and too few in a next-tree interval.
--
--   **Formalization Note** Goodness is the failure of $\mathrm{Bad}_\nu$ at the parent's scale.
--
--   Differences from the source:
--   - generalization: conditioning on P_L in the i.i.d. experiment → every fixed vector y of the first m inputs, the other N inputs i.i.d. uniform; reason: the conditional law given the prefix is this product measure, and the Lean covers every y, not only distinct values in [0,1]
--   - generalization: the inclusions for the children of the selected parents, on the run of the i.i.d. experiment → for every node of the phase tree and every input vector X; reason: the children of the selected parents and the i.i.d. inputs are special cases
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.12, p.34, displays (48), (49)

import Mathlib
import Definitions.Def_RandOrderSort_Wi
open MeasureTheory

namespace RandOrderSort

/-- **Lemma 4.12 (Arrival and next-reallocation tails)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.34: "Condition on P_L and let
1 ≤ i < k. A good selected parent J_{q,2^i s} with 2s current buckets in phase i satisfies
P(∃ child I of J_{q,2^i s} : N_i(I) > Bs | P_L) ≤ 2e^{−Bs/200}. (48) If i + 1 < k, a good selected
parent J_{q,2^{i+1}s} with 2s current buckets in phase i + 1 satisfies
P(∃ child I of J_{q,2^{i+1}s} : N_i(I) < 1.1Bs | P_L) ≤ 2e^{−Bs/65}. (49) Each event contains the
corresponding local overflow event, for current arrivals and the following reallocation,
respectively."

**Formalization Note.** For `n ≥ 8192` and `q ∈ (0,1)`. Conditioning on `P_L` is fixing a
realization `y` of the first `m` inputs, the other `N` inputs being i.i.d. `U[0,1]`. `s = 2^h`; `J_{q,2^i s}` is the fixed-tree node of height `i + h` containing `q`, its
children have height `i + h − 1`; goodness is `¬ Bad` at `ν = 2^{i+h}`. The inclusion sentence is
stated on every execution of the i.i.d. run (any input vector `X`) for every node of the phase tree
(children of the selected parents included): a phase-`i` node `(h, idx)` is the fixed-tree node
`(h + i − 1, idx)`, a phase-`(i+1)` node `(h, idx)` is `(h + i, idx)`; local overflow of the phase-`i`
arrivals in it forces `N_i(I) > Bs`, and local overflow of the reallocation at the start of phase
`i + 1` in it forces `N_i(I) < 1.1Bs`. -/
theorem lemma_4_12 : ∀ n, 16 * T ≤ n → ∀ q : ℝ, 0 < q → q < 1 → ∀ i, 1 ≤ i → i < k n →
    (∀ y : Fin (m n) → ℝ, ∀ h, 2 ^ (h + 1) ≤ b n i → ¬ Bad y q (i + h) →
      iidUnif (N n) {w | ∃ c < 2,
          B n * 2 ^ h < Nblk (joinIn y w) i (i + h - 1) (2 * parIdx (joinIn y w) q (i + h) + c)} ≤
        ENNReal.ofReal (2 * Real.exp (-((B n : ℝ) * 2 ^ h / 200)))) ∧
    (i + 1 < k n → ∀ y : Fin (m n) → ℝ, ∀ h, 2 ^ (h + 1) ≤ b n (i + 1) → ¬ Bad y q (i + 1 + h) →
      iidUnif (N n) {w | ∃ c < 2,
          (Nblk (joinIn y w) i (i + h) (2 * parIdx (joinIn y w) q (i + 1 + h) + c) : ℝ) <
            11 / 10 * (B n : ℝ) * 2 ^ h} ≤
        ENNReal.ofReal (2 * Real.exp (-((B n : ℝ) * 2 ^ h / 65)))) ∧
    ∀ X : Fin n → ℝ,
      (∀ h idx, 2 ^ h ≤ b n i →
        Overflows (opReqs (runOf X 1 1) (L n + i - 1) true) (b n i) (phaseCap n (L n + i - 1)) h idx →
          B n * 2 ^ h < Nblk X i (h + i - 1) idx) ∧
      (i + 1 < k n → ∀ h idx, 2 ^ h ≤ b n (i + 1) →
        Overflows (opReqs (runOf X 1 1) (L n + i) false) (b n (i + 1)) (phaseCap n (L n + i)) h idx →
          (Nblk X i (h + i) idx : ℝ) < 11 / 10 * (B n : ℝ) * 2 ^ h) := by sorry

end RandOrderSort
