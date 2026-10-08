-- Prove2me | Theorems.Thm_SolomonRWRE_Speed_lemma_1_9
-- name    : SolomonRWRE.Speed.lemma_1_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:12.099187+00:00
-- url     : https://prove2.me/theorems/7413329e-cd94-4a8c-9370-ffdd7b97ac58
-- title:
--   Lemma (1.9) — separated blocks of ladder times
-- statement:
--   Suppose the annealed walk has $\limsup_{n\to\infty}X_n=+\infty$ almost surely. Let $m>k$ and let $A_1,\ldots,A_k$ and $B_1,\ldots,B_j$ be sets of possible ladder times with $B_s\subseteq(0,m-k]$. Then
--
--   $$
--   P(\tau_r\in A_r\ (1\le r\le k),\ \tau_{m+s}\in B_s\ (1\le s\le j))
--   =P(\tau_r\in A_r\ (1\le r\le k))P(\tau_s\in B_s\ (1\le s\le j)).
--   $$
--
--   The formula separates an initial block of passage-time increments from a later block whose excursions are short enough to avoid the initial region.
--
--   **Formalization Note** The limsup condition comes from Theorem (1.8), in whose proof this lemma is stated. Sets are represented in $\mathbb N\cup\{\infty\}$; the condition on $B_s$ forces their members to be finite positive integers.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 5, Lemma (1.9), display (1.10), within proof of Theorem (1.8)

import Mathlib
import Definitions.Def_SolomonRWRE_Speed_Model

namespace SolomonRWRE.Speed

/-- Solomon (1975), p. 5, Lemma (1.9), display (1.10). The limit-supremum
assumption is inherited from Theorem (1.8), in whose proof this lemma occurs.
The sets are viewed in `ℕ∞`; their finite integer members are the paper's
sets `A_r, B_s ⊂ ℤ`. -/
theorem lemma_1_9 {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (h : SolomonRWRE.Recurrence.IsRWRE P α X)
    (hlim : ∀ᵐ ω ∂P, ∀ M : ℤ, ∃ᶠ n in Filter.atTop, M ≤ X n ω)
    (k j m : ℕ) (hm : k < m) (A : Fin k → Set ℕ∞) (B : Fin j → Set ℕ∞)
    (hB : ∀ s t, t ∈ B s → 0 < t ∧ t ≤ (m - k : ℕ∞)) :
    P {ω | (∀ r : Fin k, ladderTime X (r.val + 1) ω ∈ A r) ∧
      (∀ s : Fin j, ladderTime X (m + s.val + 1) ω ∈ B s)} =
      P {ω | ∀ r : Fin k, ladderTime X (r.val + 1) ω ∈ A r} *
      P {ω | ∀ s : Fin j, ladderTime X (s.val + 1) ω ∈ B s} := by sorry

end SolomonRWRE.Speed
