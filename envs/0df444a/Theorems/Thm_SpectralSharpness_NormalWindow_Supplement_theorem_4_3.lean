-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_4_3
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:15:43.092117+00:00
-- url     : https://prove2.me/theorems/3668eaed-d230-4294-bd77-b13242a8ec0b
-- title:
--   Theorem 4.3 — sharp window bounds
-- statement:
--   For a positive odd integer d and 0<γ<1, let S_d and σ_d be the square-wave truncation and Fejér sum. Both connected-component window bounds are asserted.
--
--   Theorem 4.3 (sharp window bounds). For every odd d and every γ ∈ (0, 1):
--   w_γ(S_d) ≥ πγ/(d + 1), w_γ(σ_d) ≥ 2πγ/(d + 1).
--
--   $$
--   w_\gamma(S_d)\ge\frac{\pi\gamma}{d+1},\qquad w_\gamma(\sigma_d)\ge\frac{2\pi\gamma}{d+1}.
--   $$
--
--   This statement supplies the source’s independent companion result alongside the published normal-window goal.
--
--   Differences from the source:
--   - encoding: odd positive integer d and d tending to infinity through odd integers → d=2m+1 with m a natural number tending to infinity; reason: this parametrizes exactly the permitted degrees, including d=1
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 4.3, p. 10

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_4_3 (m : ℕ) (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    window γ (truncation (oddDegree m)) ≥ Real.pi*γ/((oddDegree m:ℝ)+1) ∧
    window γ (fejer (oddDegree m)) ≥ 2*Real.pi*γ/((oddDegree m:ℝ)+1) := by sorry

end SpectralSharpness.NormalWindow.Supplement
