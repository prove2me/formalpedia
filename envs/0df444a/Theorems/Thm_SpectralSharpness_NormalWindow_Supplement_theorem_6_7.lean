-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_6_7
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:19:11.764216+00:00
-- url     : https://prove2.me/theorems/a9746974-7af2-4f87-ba34-ba3e6fe5c728
-- title:
--   Theorem 6.7 — the primitive of the step is affine
-- statement:
--   Let J be the periodic accumulator ∫₀ˣ applied to the mean-zero square wave H=sgn(sin). The periodic extension identifies the endpoints ±π. Both Fourier series below are asserted to converge absolutely.
--
--   Theorem 6.7 (the primitive of the step is affine). J H is the 2π-periodic triangle wave:
--   (J H)(x) = |x| for |x| ≤ π, hence (J H)(x) = x on [0, π],
--   and
--   (J H)(x) = (4/π) ∑_{k≥1, k odd} (1 − cos kx)/k² = π/2 − (4/π) ∑_{k≥1, k odd} (cos kx)/k².
--
--   $$
--   (JH)(x)=|x|\ (|x|\le\pi),\qquad(JH)(x)=\frac4\pi\sum_{\substack{k\ge1\\k\ \mathrm{odd}}}\frac{1-\cos(kx)}{k^2}=\frac\pi2-\frac4\pi\sum_{\substack{k\ge1\\k\ \mathrm{odd}}}\frac{\cos(kx)}{k^2}.
--   $$
--
--   This statement supplies the source’s independent companion result alongside the published normal-window goal.
--
--   Differences from the source:
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
--   - encoding: infinite absolutely convergent series → tsum expressions together with Summable of absolute values; reason: the actual infinite series is used, not a finite truncation
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 6.7, pp. 15–16

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_6_7 :
    Function.Periodic (accumulator squareWave) (2*Real.pi) ∧
    (∀ x, |x| ≤ Real.pi → accumulator squareWave x=|x|) ∧
    (∀ x ∈ Set.Icc (0:ℝ) Real.pi, accumulator squareWave x=x) ∧
    (∀ x, Summable (fun k : ℕ => |if 0 < k ∧ Odd k then (1-Real.cos ((k:ℝ)*x))/(k:ℝ)^2 else 0|) ∧
      Summable (fun k : ℕ => |if 0 < k ∧ Odd k then Real.cos ((k:ℝ)*x)/(k:ℝ)^2 else 0|) ∧
      accumulator squareWave x = 4/Real.pi *
        ∑' k : ℕ, if 0 < k ∧ Odd k then (1-Real.cos ((k:ℝ)*x))/(k:ℝ)^2 else 0) ∧
    (∀ x, accumulator squareWave x = Real.pi/2 - 4/Real.pi *
      ∑' k : ℕ, if 0 < k ∧ Odd k then Real.cos ((k:ℝ)*x)/(k:ℝ)^2 else 0) := by sorry

end SpectralSharpness.NormalWindow.Supplement
