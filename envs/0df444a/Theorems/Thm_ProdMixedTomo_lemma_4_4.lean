-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_4_4
-- name    : ProdMixedTomo.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:23.288498+00:00
-- url     : https://prove2.me/theorems/1a745180-4e86-4647-9bba-135fe9efe874
-- title:
--   Lemma 4.4 — the filter update removes more weight from the bad points
-- statement:
--   Let $\tau\in\mathbb R^N\setminus\{0\}$ be entrywise nonnegative, $w\in\Gamma_N$, and $[N]=A\cup B$ with $A,B$ disjoint, and assume
--   $$
--   \sum_{i\in A}w_i\tau_i\le\sum_{i\in B}w_i\tau_i .
--   $$
--   Let $\tau_{\max}=\max_{i:\,w_i>0}\tau_i>0$ and $w'_i=(1-\tau_i/\tau_{\max})w_i$. Then $\mathrm{nnz}(w')<\mathrm{nnz}(w)$ and
--   $$
--   \sum_{i\in A}(w_i-w'_i)\le\sum_{i\in B}(w_i-w'_i).
--   $$
--   It is the invariant of the weighted filter: scores larger on average on the bad points make each update remove more bad than good weight, and every update zeroes at least one point.
--
--   Differences from the source:
--   - encoding: τ_max = max_{i : wᵢ > 0} τᵢ > 0 → a real τ_max attained at some i with wᵢ > 0, bounding τᵢ for every i with wᵢ > 0, and positive; reason: the two properties of the maximum, which exists since the hypotheses give some wᵢ > 0
--   - encoding: S = A ∪ B for disjoint A, B → A ∪ B = all N indices, A and B disjoint; reason: indices are associated with points (p.21)
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.4, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ProdMixedTomo_Weights

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.4, p.22 (PDF p.24). Let `τ ∈ ℝ^N \ {0}` be entrywise nonnegative, `w ∈ Γ_N`, and
`[N] = A ∪ B` with `A, B` disjoint and `Σ_{i∈A} wᵢτᵢ ≤ Σ_{i∈B} wᵢτᵢ`. Let
`τ_max = max_{i : wᵢ > 0} τᵢ > 0` and `w'ᵢ = (1 − τᵢ/τ_max) wᵢ`. Then `nnz(w') < nnz(w)` and
`Σ_{i∈A}(wᵢ − w'ᵢ) ≤ Σ_{i∈B}(wᵢ − w'ᵢ)`.

**Formalization Note.** `τ_max` is given with the two properties that make it the maximum of
`τ` over `{i : wᵢ > 0}` (attained, and an upper bound); its positivity is the printed hypothesis. -/
theorem lemma_4_4 (N : ℕ) (τ w : Fin N → ℝ) (A B : Finset (Fin N)) (τmax : ℝ)
    (hτ0 : τ ≠ 0) (hτ : ∀ i, 0 ≤ τ i) (hw : w ∈ Gamma N) (hAB : Disjoint A B)
    (hcover : A ∪ B = Finset.univ)
    (hscore : ∑ i ∈ A, w i * τ i ≤ ∑ i ∈ B, w i * τ i)
    (hmax_mem : ∃ i, 0 < w i ∧ τ i = τmax) (hmax_ge : ∀ i, 0 < w i → τ i ≤ τmax)
    (hpos : 0 < τmax) :
    nnz (fun i => (1 - τ i / τmax) * w i) < nnz w ∧
      ∑ i ∈ A, (w i - (1 - τ i / τmax) * w i) ≤ ∑ i ∈ B, (w i - (1 - τ i / τmax) * w i) := by sorry

end ProdMixedTomo
