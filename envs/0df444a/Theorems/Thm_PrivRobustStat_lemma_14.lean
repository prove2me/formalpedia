-- Prove2me | Theorems.Thm_PrivRobustStat_lemma_14
-- name    : PrivRobustStat.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:20.063662+00:00
-- url     : https://prove2.me/theorems/0dad2641-fa59-4432-a7f5-ba909fc7530d
-- title:
--   Lemma 14, p.32 — Algorithm 7 is $(\lambda,1024R_0^2(d+\log(2/\beta))/(n^2\eta^2))$-RDP and $\eta$-accurate
-- statement:
--   **Lemma 14** (private weighted mean). Let $q\in\mathbb R^d$, $R_0,\eta>0$, $\beta\in(0,\tfrac14)$.
--
--   1. If the weights of Algorithm 7 satisfy Property 1 ($w_i=f_i(z_i)$ for public $f_i:\mathbb R^d\to[0,\tfrac1n]$), then for every $\lambda>1$ the output $c$ is
--   $$\Big(\lambda,\ \frac{1024R_0^2(d+\log(2/\beta))}{n^2\eta^2}\Big)\text{-RDP}$$
--   over neighbouring datasets $z_{[n]}\subset B(q,R_0)$.
--   2. If $z_{[n]}\subset B(q,R_0)$, $w\in[0,\tfrac1n]^n$, $\|w\|_1\ge\tfrac34$ and $\eta\le R_0/4$, then with probability at least $1-\beta$,
--   $$\|c-\hat\mu(w)\|_2\le\eta .$$
--
--   This is the private recentering step used in every round of Algorithm 8.
--
--   Differences from the source:
--   - encoding: input weights satisfying Property 1 → w_i = f_i(x_i) for public weight functions f_i : ℝ^d → [0, 1/n] fixed before the dataset; reason: Property 1 with the preceding query history public
--   - encoding: "Algorithm 7 satisfies (λ, ρ)-RDP" → RDP over neighbouring datasets that both lie in B(q, R₀); reason: z[n] ⊂ B(q, R₀) is Algorithm 7's input condition
--   - encoding: the output law of the mechanism → the law is the pushforward of the noise measure, and the item also asserts the output map is measurable; reason: Lean pushes a non-measurable map to the zero measure, under which privacy would hold vacuously; measurability rules this out and changes no instance
--   - generalization: accuracy for input weights satisfying Property 1 → accuracy for every w ∈ [0, 1/n]^n with ∥w∥₁ ≥ 3/4 and every dataset in B(q, R₀); reason: the accuracy claim does not use Property 1; Property-1 weights on a fixed dataset are such w
--   - encoding: with probability at least 1 − β → a measurable event of the Gaussian draws with that probability; reason: avoids outer measure; same claim
--   - encoding: "It runs in time O(nd)" → not in this item; the mission goal theorem_4 bounds the work of a machine program; reason: the item states the algorithm as a random map of data and noise, which has no cost (planning decision 10)
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), Lemma 14, p.32 (PDF p.35); Algorithm 7, p.32

import Mathlib
import Definitions.Def_PrivRobustStat_MeanEst

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-- **Lemma 14** (private weighted mean), p.32 (PDF p.35).

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…).

"Suppose that the input w to Algorithm 7 satisfies Property 1. Then for every λ > 1, Algorithm 7
satisfies (λ, 1024R₀²(d + log(2/β))/(n²η²))-RDP. If ∥w∥₁ ≥ 3/4 and η ≤ R₀/4, then
∥c − µ̂(w)∥₂ ≤ η with probability ≥ 1 − β. It runs in time O(nd)."

**Formalization Note.** Algorithm 7's inputs: a dataset `z[n] ⊂ B(q, R₀)`, internal weights
`w ∈ [0, 1/n]^n`, public `q`, `R₀, η > 0`, `β ∈ (0, 1/4)`. For privacy the weights are
`w_i := f i (z_i)` with public weight functions `f` (Property 1), and RDP is over neighbouring
datasets both in `B(q, R₀)`; the first part also asserts the output is a measurable function of the
Gaussian draws. The accuracy claim holds for every `w ∈ [0, 1/n]^n` with `∥w∥₁ ≥ 3/4`, with
`µ̂(w)` the weighted mean of `z` (`wMean z w`), on a measurable event of probability `≥ 1 − β`. The
running time is carried by the goal theorem's time clause. -/
theorem lemma_14 {d n : ℕ} (q : Vec d) (R0 η β : ℝ) (hR0 : 0 < R0) (hη : 0 < η) (hβ : 0 < β)
    (hβ' : β < 1 / 4) :
    (∀ f : Fin n → Vec d → ℝ, IsWeightFn n f →
      (∀ z : Fin n → Vec d, Measurable fun g : Option (Fin d) → ℝ =>
        alg7 z (fun i => f i (z i)) q R0 η β g) ∧
      ∀ lam : ℝ, 1 < lam →
        IsRDPOn (fun z : Fin n → Vec d => ∀ i, ‖z i - q‖ ≤ R0) lam
          (1024 * R0 ^ 2 * ((d : ℝ) + Real.log (2 / β)) / ((n : ℝ) ^ 2 * η ^ 2))
          (fun z => (stdGauss (Option (Fin d))).map fun g => alg7 z (fun i => f i (z i)) q R0 η β g)) ∧
    ∀ z : Fin n → Vec d, (∀ i, ‖z i - q‖ ≤ R0) → ∀ w : Fin n → ℝ, InBox n w →
      3 / 4 ≤ l1 w → η ≤ R0 / 4 →
      ∃ E : Set (Option (Fin d) → ℝ), MeasurableSet E ∧
        ENNReal.ofReal (1 - β) ≤ stdGauss (Option (Fin d)) E ∧
        ∀ g ∈ E, ‖alg7 z w q R0 η β g - wMean z w‖ ≤ η := by sorry

end PrivRobustStat
