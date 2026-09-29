-- Prove2me | Theorems.Thm_VapnikChervonenkis_Entropy_eq26_index_exceeds_phi
-- name    : VapnikChervonenkis.Entropy.eq26_index_exceeds_phi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:09:44.184423+00:00
-- url     : https://prove2.me/theorems/8f4ebb4d-f8af-4b5a-83a2-5dfde071247a
-- title:
--   (26) — P{Δ^S(x_1, …, x_l) > Φ([ql], l)} → 1 when q log₂(2e/q) < c
-- statement:
--   Let $(X, P)$ be a probability space and $S$ a collection of subsets of $X$ such that the index is a measurable function of the sample for every $l$. Suppose $H^S(l)/l \to c$, and let $q$ satisfy $0 < q < \tfrac14$ and
--
--   $$
--   q \log_2 \frac{2e}{q} < c . \tag{25}
--   $$
--
--   Then, with $n = [ql]$ the integer part of $ql$,
--
--   $$
--   \lim_{l \to \infty} \mathbf{P}\bigl\{\Delta^S(x_1, \dots, x_l) > \Phi([ql], l)\bigr\} = 1 .
--   $$
--
--   Combined with Lemma 1, this says that a typical sample of size $l$ contains a subsample of size proportional to $l$ on which $S$ induces every subsample; this is the combinatorial core of the necessity half of Theorem 4.
--
--   **Formalization Note.** $[ql]$ is the natural-number floor `⌊q * l⌋₊`. The limit $c$ enters as a hypothesis. Condition (25) forces $c > 0$, since $q \log_2(2e/q) > 0$ for $0 < q < \tfrac14$; no separate positivity assumption is added. The measurability of the index is the paper's own assumption (p. 273).
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 277, proof of necessity of Theorem 4, step 2°, Eq. (26) (under (25))

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- Display (26) in step 2° of the proof of necessity in Theorem 4 (p. 277): let `c` be the limit
of `H^S(l)/l`, and let `q` satisfy `0 < q < 1/4` and (25) `q log₂(2e/q) < c`. Then
`lim_{l→∞} P{Δ^S(x_1, ···, x_l) > Φ(n, l)} = 1` for `n = [ql]` (the integer part `⌊q l⌋`).
`hΔ` is the paper's assumption (p. 273) that the index is a measurable function of the sample. -/
theorem eq26_index_exceeds_phi {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (c q : ℝ)
    (hc : Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 c))
    (hq0 : 0 < q) (hq : q < 1 / 4) (h25 : q * Real.logb 2 (2 * Real.exp 1 / q) < c) :
    Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
        {x | Shared.Phi ⌊q * (l : ℝ)⌋₊ l < Shared.index S x}) atTop (𝓝 1) := by sorry

end VapnikChervonenkis.Entropy
