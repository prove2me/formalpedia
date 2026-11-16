-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_5_1
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:17:16.184428+00:00
-- url     : https://prove2.me/theorems/124a212c-2d58-45ba-9b90-064e80b9a38a
-- title:
--   Theorem 5.1 — computable ⇒ continuous
-- statement:
--   A real function on [−π,π] is computable when one finite oracle procedure transforms every Cauchy name of every real input into rational output approximations of every requested precision. The domain of the theorem is all total functions, without continuity built into that domain.
--
--   Theorem 5.1 (computable ⇒ continuous). Every total computable function f : [−π, π] → R
--   is continuous. In particular the ideal classifier H = sgn sin is not Turing-computable, and neither is
--   any classifier with a nonempty jump set.
--
--   $$
--   f:[-\pi,\pi]\to\mathbb R\ \text{total and Type-2 computable}\quad\Longrightarrow\quad f\ \text{continuous}.
--   $$
--
--   This statement supplies the source’s independent companion result alongside the published normal-window goal.
--
--   Differences from the source:
--   - encoding: TTE on the closed interval → one finite oracle program on every rational Cauchy name, with an unrestricted function as target; reason: all input reals and equivalent names are included
--   - generalization: no classifier with a nonempty jump set is computable → every function with a point of discontinuity on the interval is noncomputable; reason: a jump is a discontinuity, so the source instance is included
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 5.1, p. 12

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Computability

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_5_1 :
    (∀ f : ℝ → ℝ, typeTwoComputable (Set.Icc (-Real.pi) Real.pi) f →
      ContinuousOn f (Set.Icc (-Real.pi) Real.pi)) ∧
    ¬ typeTwoComputable (Set.Icc (-Real.pi) Real.pi) squareWave ∧
    (∀ f : ℝ → ℝ, (∃ x ∈ Set.Icc (-Real.pi) Real.pi,
      ¬ ContinuousWithinAt f (Set.Icc (-Real.pi) Real.pi) x) →
      ¬ typeTwoComputable (Set.Icc (-Real.pi) Real.pi) f) := by sorry

end SpectralSharpness.NormalWindow.Supplement
