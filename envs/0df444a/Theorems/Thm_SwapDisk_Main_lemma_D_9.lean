-- Prove2me | Theorems.Thm_SwapDisk_Main_lemma_D_9
-- name    : SwapDisk.Main.lemma_D_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:16:24.772838+00:00
-- url     : https://prove2.me/theorems/cd887915-cc28-4c6c-9511-858d17031afc
-- title:
--   Lemma D.9 — optimal averaged support of an inscribed dictionary: $\int_{S^1}h_A\,d\sigma\le1-\beta_N$, sharp; $2/(3N^2)\le\beta_N\le\pi^2/(6N^2)$
-- statement:
--   Let $N\ge1$. If $A\subseteq B^2_2$ is nonempty and finite with $|A|\le N$, then
--   $$\int_{S^1}h_A(u)\,d\sigma(u)\le1-\beta_N .$$
--   Equality is attained by $N$ equally spaced unit-circle points, including the one-point case. Furthermore
--   $$\frac2{3N^2}\le\beta_N\le\frac{\pi^2}{6N^2},\qquad\Big|\beta_N-\frac{\pi^2}{6N^2}\Big|\le\frac{\pi^4}{120N^4}.$$
--
--   This is the geometric deficit that a fixed dictionary pays against a random direction.
--
--   Differences from the source:
--   - encoding: N equally spaced unit-circle points → for every θ₀, the points (cos(θ₀ + 2πk/N), sin(θ₀ + 2πk/N)), k < N; reason: these are all configurations of N equally spaced points
--   - encoding: ∫_{S¹} h_A dσ with σ normalized arc measure → Bochner integral of `supportFn A` against `arcMeasure` (image of dθ/2π on [0, 2π)); reason: same measure; h_A is continuous and bounded
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 47, Lemma D.9

import Mathlib
import Definitions.Def_SwapDisk_Main_Geometry

open MeasureTheory

namespace SwapDisk.Main

/-- Lemma D.9 (Optimal averaged support of an inscribed dictionary), p. 47: for a nonempty
finite `A ⊆ B²₂` with `|A| ≤ N`, `∫_{S¹} h_A dσ ≤ 1 − β_N`; equality for every configuration of
`N` equally spaced unit-circle points (including `N = 1`); `2/(3N²) ≤ β_N ≤ π²/(6N²)` and
`|β_N − π²/(6N²)| ≤ π⁴/(120N⁴)`. -/
theorem lemma_D_9 (N : ℕ) (hN : 1 ≤ N) :
    (∀ (A : Finset E2) (hA : A.Nonempty), (↑A : Set E2) ⊆ disk → A.card ≤ N →
      ∫ u, supportFn A hA u ∂arcMeasure ≤ 1 - betaN N) ∧
    (∀ θ₀ : ℝ, ∃ hP : (Finset.univ.image
        (fun k : Fin N => circlePt (θ₀ + 2 * Real.pi * k / N))).Nonempty,
      ∫ u, supportFn _ hP u ∂arcMeasure = 1 - betaN N) ∧
    2 / (3 * (N : ℝ) ^ 2) ≤ betaN N ∧ betaN N ≤ Real.pi ^ 2 / (6 * (N : ℝ) ^ 2) ∧
    |betaN N - Real.pi ^ 2 / (6 * (N : ℝ) ^ 2)| ≤ Real.pi ^ 4 / (120 * (N : ℝ) ^ 4) := by sorry

end SwapDisk.Main
