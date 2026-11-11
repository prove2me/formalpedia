-- Prove2me | Theorems.Thm_TestableSanitization_Robust_lemma_38
-- name    : TestableSanitization.Robust.lemma_38
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:52:39.650359+00:00
-- url     : https://prove2.me/theorems/48e77367-bc86-4496-81df-d1b092afb9fe
-- title:
--   Lemma 38 — uniform-ball estimates: $\mathbb E\langle W,e\rangle^2=\tfrac{s^2}{d+2}\le\tfrac{s^2}d$ and $\Pr[\langle W,e\rangle>t]\le\tfrac{s^2}{2dt^2}$
-- statement:
--   Let $d\ge1$ and $s>0$, let $W$ be uniform on the closed ball $B_s=\{w\in\mathbb R^d:\|w\|\le s\}$, and let $e$ be a unit vector. Then
--   $$\mathbb E\langle W,e\rangle^2=\frac{s^2}{d+2}\le\frac{s^2}{d},\qquad \Pr[\langle W,e\rangle>t]\le\frac{s^2}{2dt^2}\quad(t>0).$$
--
--   These are the estimates behind Lemma 10: a uniform perturbation of radius $s$ rarely moves far in a fixed direction, so a ball of radius $s$ around any point near $x$ mostly lies inside the ball of radius $L$ around $x$.
--
--   Differences from the source:
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: W uniform on B_s (a ball of radius s > 0), ⟨·,·⟩ the Euclidean inner product → expectation and probability under ballLaw 0 s with 0 < s, inner ℝ w e; reason: the law of W; radii are positive throughout §2
--   - encoding: Pr[⟨W, e⟩ > t] as a real probability → the measure of {w | t < ⟨w, e⟩} in [0, ∞], bounded by ENNReal.ofReal (s²/(2dt²)); reason: same value; ENNReal convention
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 72 (PDF 74), Lemma 38

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary

open MeasureTheory

namespace TestableSanitization.Robust

theorem lemma_38 (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s) (e : Pt d) (he : ‖e‖ = 1) :
    ∫ w, (inner ℝ w e) ^ 2 ∂(ballLaw 0 s) = s ^ 2 / ((d : ℝ) + 2) ∧
      s ^ 2 / ((d : ℝ) + 2) ≤ s ^ 2 / d ∧
      ∀ t : ℝ, 0 < t →
        ballLaw 0 s {w | t < inner ℝ w e} ≤ ENNReal.ofReal (s ^ 2 / (2 * d * t ^ 2)) := by sorry

end TestableSanitization.Robust
