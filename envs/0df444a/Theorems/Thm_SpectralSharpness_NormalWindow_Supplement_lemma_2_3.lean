-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_lemma_2_3
-- name    : SpectralSharpness.NormalWindow.Supplement.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:07:06.596318+00:00
-- url     : https://prove2.me/theorems/50904c79-cb55-4b63-a3c4-b07d8247e64a
-- title:
--   Lemma 2.3 — Gibbs overshoot and Fejér positivity
-- statement:
--   For m≥0 put d=2m+1 and let S_d, σ_d and Φ be the square-wave truncation, its Fejér mean and the Gibbs profile. Put A_d=sup|S_d| and G=Φ(π). The assertion includes the following four clauses, together with the monotone convergence of A_d.
--
--   Lemma 2.3 (Gibbs overshoot and Fejér positivity). For every odd d: (i) S_d(0) = σ_d(0) = 0,
--   S_d′(0) = 2(d + 1)/π, σ_d′(0) = (d + 1)/π; (ii) A_d := ∥S_d∥∞ = sup_{x∈(0,π)} S_d(x) satisfies A_d ↓ G where
--   G = (2/π) ∫_0^π (sin t)/t dt = 1.1789797444 . . . , g := G − 1 = 0.1789797444 . . . (Gibbs’ constant);
--   (iii) 0 ≤ S_d(x) ≤ A_d for x ∈ (0, π); (iv) |σ_d(x)| ≤ 1 for all x.
--
--   $$
--   S_d'(0)=\frac{2(d+1)}\pi,\quad \sigma_d'(0)=\frac{d+1}\pi,\quad A_d\downarrow G=\frac2\pi\int_0^\pi\frac{\sin t}{t}\,dt,\quad |\sigma_d|\le1.
--   $$
--
--   This statement supplies the source’s supporting result for the associated companion theorem.
--
--   Differences from the source:
--   - encoding: odd positive integer d and d tending to infinity through odd integers → d=2m+1 with m a natural number tending to infinity; reason: this parametrizes exactly the permitted degrees, including d=1
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Lemma 2.3, p. 7

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- All four printed clauses, with odd d=2m+1. -/
theorem lemma_2_3 :
  (∀ m, truncation (oddDegree m) 0=0 ∧ fejer (oddDegree m) 0=0 ∧
    deriv (truncation (oddDegree m)) 0 = 2*((oddDegree m:ℝ)+1)/Real.pi ∧
    deriv (fejer (oddDegree m)) 0 = ((oddDegree m:ℝ)+1)/Real.pi) ∧
  (∀ m, supNorm (truncation (oddDegree m)) =
    sSup ((truncation (oddDegree m)) '' Set.Ioo 0 Real.pi)) ∧
  Antitone (fun m => supNorm (truncation (oddDegree m))) ∧
  Tendsto (fun m => supNorm (truncation (oddDegree m))) atTop (nhds gibbsConstant) ∧
  (∀ m x, x ∈ Set.Ioo 0 Real.pi → 0 ≤ truncation (oddDegree m) x ∧
    truncation (oddDegree m) x ≤ supNorm (truncation (oddDegree m))) ∧
  (∀ m x, |fejer (oddDegree m) x| ≤ 1) := by sorry

end SpectralSharpness.NormalWindow.Supplement
