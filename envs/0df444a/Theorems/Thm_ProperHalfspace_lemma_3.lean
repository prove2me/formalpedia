-- Prove2me | Theorems.Thm_ProperHalfspace_lemma_3
-- name    : ProperHalfspace.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:49.11613+00:00
-- url     : https://prove2.me/theorems/2d7de6d2-6fba-4b98-88cb-c60c8d1d6d01
-- title:
--   Lemma 3 — coordinate resampling
-- statement:
--   Let $f,g:\{\pm1\}^n\to[-1,1]$ and $J\subseteq[n]$, and let $g_J(x)=\mathbf E_{y_J\sim\{\pm1\}^J}[g(y_J,x_{-J})]$ be $g$ with the coordinates of $J$ resampled. Then
--   $$\bigl|\mathbf E_x[f(x)g(x)]-\mathbf E_x[f(x)g_J(x)]\bigr|\le\sqrt{\sum_{i\in J}\mathrm{Inf}_i[f]}.$$
--
--   Resampling a set of low-influence coordinates therefore changes the correlation with a bounded function only slightly.
--
--   Differences from the source:
--   - encoding: the average over y_J ∈ {±1}^J → the average over a full cube point y, whose coordinates off J are ignored; reason: same value
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Lemma 3, p.12

import Mathlib
import Definitions.Def_ProperHalfspace_Fourier

namespace ProperHalfspace

/-- Lemma 3, p.12 (coordinate resampling). De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026).
`|E[f g] − E[f g_J]| ≤ √(Σ_{i ∈ J} Inf_i[f])` for `f, g : {±1}ⁿ → [−1, 1]`. -/
theorem lemma_3 {n : ℕ} (f g : Cube n → ℝ) (hf : IsBoundedOne f) (hg : IsBoundedOne g)
    (J : Finset (Fin n)) :
    |cubeAvg (fun x => f x * g x) - cubeAvg (fun x => f x * resample J g x)| ≤
      Real.sqrt (∑ i ∈ J, influence f i) := by sorry

end ProperHalfspace
