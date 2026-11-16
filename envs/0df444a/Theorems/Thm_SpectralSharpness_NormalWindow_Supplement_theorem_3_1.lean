-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_3_1
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:07:35.011932+00:00
-- url     : https://prove2.me/theorems/8f383308-2c65-47ba-b47c-aea55e365ab1
-- title:
--   Theorem 3.1 — worst case ≠ average case
-- statement:
--   For every positive odd d, let H=sgn(sin), S_d its actual finite Fourier truncation, and T_d=∑_{k>d, k odd}k^(−2). Essential supremum error is distinguished from ordinary Lebesgue L² error on [−π,π).
--
--   Theorem 3.1 (worst case ≠ average case). For every odd d ≥ 1:
--   ∥S_d − H∥_{L∞(T)} = 1 exactly,
--   whereas
--   ∥S_d − H∥_{L²} = √((16/π) ∑_{k>d, k odd} 1/k²) = √(8/(πd)) (1 + O(1/d)) → 0 as d → ∞.
--
--   $$
--   \|S_d-H\|_{L^\infty}=1,\qquad\|S_d-H\|_2=\sqrt{\frac{16}{\pi}\sum_{\substack{k>d\\ k\ \mathrm{odd}}}\frac1{k^2}}=\sqrt{\frac8{\pi d}}\bigl(1+O(d^{-1})\bigr)\longrightarrow0.
--   $$
--
--   This statement supplies the source’s independent companion result alongside the published normal-window goal.
--
--   Differences from the source:
--   - encoding: odd positive integer d and d tending to infinity through odd integers → d=2m+1 with m a natural number tending to infinity; reason: this parametrizes exactly the permitted degrees, including d=1
--   - reading: §2 says normalized Lebesgue L², while the displayed identities and proofs use ‖sin(kx)‖₂²=π → ordinary Lebesgue L² on one period; reason: the proof fixes the displayed constants; the ordinary norm is √(2π) times the normalized norm
--   - encoding: O, o, Θ or Ω asymptotic notation → actual big-O, two-sided asymptotic bounds, limits or eventual inequalities at the stated filter; reason: quantifiers constrain the actual functions rather than an independent error term
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 3.1, p. 8

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_3_1 :
  (∀ m, linfty (fun x => truncation (oddDegree m) x-squareWave x)=1 ∧
    ltwo (fun x => truncation (oddDegree m) x-squareWave x) =
      Real.sqrt (16/Real.pi*tailSquares (oddDegree m))) ∧
  Asymptotics.IsBigO atTop
    (fun m => ltwo (fun x => truncation (oddDegree m) x-squareWave x) /
      Real.sqrt (8/(Real.pi*(oddDegree m:ℝ)))-1)
    (fun m => 1/(oddDegree m:ℝ)) ∧
  Tendsto (fun m => ltwo (fun x => truncation (oddDegree m) x-squareWave x)) atTop (nhds 0) := by sorry

end SpectralSharpness.NormalWindow.Supplement
