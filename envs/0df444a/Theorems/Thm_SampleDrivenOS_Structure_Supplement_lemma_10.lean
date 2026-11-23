-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_Supplement_lemma_10
-- name    : SampleDrivenOS.Structure.Supplement.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:47:04.39427+00:00
-- url     : https://prove2.me/theorems/eea16023-4a27-4ccb-9aab-5bbfcdb564c1
-- title:
--   Lemma 10 — monotonicity of each fixed threshold guarantee
-- statement:
--   Fix 0≤p<1 and a nondecreasing feasible threshold sequence t. Let β_{N,p}(t) be the worst-case expected competitive ratio of the actual threshold algorithm under independent sampling. For every N≥1,
--   $$
--   \beta_{N,p}(t)\ge\beta_{N+1,p}(t).
--   $$
--   The same thresholds are used for both population sizes. This is the monotonicity supporting the decreasing-limit assertion in Theorem 12.
--
--   Differences from the source:
--   - encoding: feasible threshold vector in the governing §4.4 setup → t₀=p and p≤t₁≤t₂≤⋯≤1, with positive integer N; reason: the unused index 0 fixes the shared convention; no admissible threshold vector is excluded
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 18, Lemma 10

import Definitions.Def_SampleDrivenOS_Structure_Supplement_Thresholds

namespace SampleDrivenOS.Structure.Supplement

theorem lemma_10 (p : ℝ) (hp : 0 ≤ p ∧ p < 1) (t : ℕ → ℝ)
    (ht : IsThresholds p t) (N : ℕ) (hN : 1 ≤ N) :
    thresholdRatio (N + 1) p t ≤ thresholdRatio N p t := by sorry

end SampleDrivenOS.Structure.Supplement
