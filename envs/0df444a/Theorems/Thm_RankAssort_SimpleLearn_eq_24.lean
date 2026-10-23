-- Prove2me | Theorems.Thm_RankAssort_SimpleLearn_eq_24
-- name    : RankAssort.SimpleLearn.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:31.574259+00:00
-- url     : https://prove2.me/theorems/896edfba-a684-4e55-a2d1-13d175c11969
-- title:
--   (24), p. 58 — union bound: with probability ≥ 1 − δ every rank of π̃ satisfies (23)
-- statement:
--   Let $\delta > 0$ and $\epsilon' \in \mathbb R$, and consider a run of the Simple Learning Algorithm (Algorithm 2) driven by an $(\epsilon', \delta/n)$-PAC black box, in the prefix-conditional sense of the definition `SimpleLearningRun`. Let $B_r$ be the event that the product placed at rank $r$ is $\epsilon'$-approximately best among the products not ranked before it, i.e. that (23) holds at rank $r$. Then
--
--   $$
--   \Pr\bigl(B_r \text{ holds for all } r \in [n]\bigr) \ \ge\ 1 - \sum_{r=1}^{n}\Pr(B_r \text{ fails}) \ \ge\ 1 - n\cdot\frac{\delta}{n} = 1-\delta .
--   $$
--
--   The page bounds each $\Pr(B_r = 0)$ by $\delta/n$ and applies the union bound. The per-rank bound is obtained here by summing the prefix-conditional guarantee over the possible prefixes.
--
--   **Formalization Note** Ranks are 0-based in Lean: the paper's rank $r$ is index $r-1$, a ranking is a duplicate-free list of the $n$ products (`Fin n`), and $\pi^{-1}(j)$ is the list entry at index $j-1$. The probability is the measure $P$ of the learning randomness; $1-\delta$ enters as `ENNReal.ofReal (1 - delta)`. The theorem is stated for an arbitrary tolerance $\epsilon'$; Theorem 3 uses $\epsilon' = 2\epsilon/n$.
--
--   Differences from the source:
--   - generalization: ϵ′ = 2ϵ/n → any real tolerance epsP; reason: Theorem 3 uses the instance epsP = 2ϵ/n
--   - generalization: D a distribution of customer types → any measure D on the type space; reason: the statement concerns only the learning probability P; a probability measure D is one instance
--   - reading: Pr(B_r = 0) ≤ δ/n for every r, from the (ϵ′, δ/n)-PAC guarantee → the prefix-conditional PAC guarantee of SimpleLearningRun, summed over prefixes; reason: p. 58: "(23) holds for any particular instantiation of [π̃]ᵣ₋₁ with probability 1 − δ/n"; summing over prefixes gives the page's per-rank bound
--   - encoding: Pr over the algorithm's randomness, value 1 − δ → measure P of the learning randomness Ω, ENNReal.ofReal (1 − delta); reason: Lean convention; same values for δ ≤ 1, and both sides trivial for δ > 1
--   - encoding: ranks 1..n, a ranking is a permutation π of [n], π⁻¹(j) the product at rank j → 0-based indices, a ranking is a duplicate-free List (Fin n) of length n, π⁻¹(j) is the entry at index j − 1; reason: Lean convention; the same rankings
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 58, (24), proof of Theorem 3

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Algorithm

namespace RankAssort.SimpleLearn
open MeasureTheory
theorem eq_24 {n : ℕ} {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) (τ : Θ → CustomerType n)
    (epsP delta : ℝ) (hdelta : 0 < delta)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : SimpleLearningRun D τ epsP (delta / n) P) :
    ENNReal.ofReal (1 - delta) ≤
      P {ω | ∀ r < n, ∃ i, (run.out ω)[r]? = some i ∧
              IsApproxBest D τ ((run.out ω).take r) i epsP} := by sorry
end RankAssort.SimpleLearn
