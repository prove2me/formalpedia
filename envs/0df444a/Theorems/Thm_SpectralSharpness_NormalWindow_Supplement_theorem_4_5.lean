-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_4_5
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:16:34.776039+00:00
-- url     : https://prove2.me/theorems/99a56ae7-fcd4-4e8d-91fc-19955e943fbf
-- title:
--   Theorem 4.5 — upper bound
-- statement:
--   Fix 0<γ<1 and let d run through positive odd integers. U_γ(S_d) is the entire uncertain region, while w_γ(S_d) is its component containing zero. Norms below use ordinary Lebesgue length.
--
--   Theorem 4.5 (upper bound). For every odd d and γ ∈ (0, 1),
--   |U_γ(S_d)| ≤ ∥H − S_d∥₂²/(1 − γ)² = (16/(π(1 − γ)²)) ∑_{k>d, k odd} 1/k² = (8/(πd(1 − γ)²)) (1 + O(1/d)).
--   Consequently w_γ(S_d) = Θ_γ(1/d): the uncertainty window shrinks at rate exactly 1/d and no faster.
--
--   $$
--   |U_\gamma(S_d)|\le\frac{\|H-S_d\|_2^2}{(1-\gamma)^2}=\frac{16}{\pi(1-\gamma)^2}\sum_{\substack{k>d\\k\ \mathrm{odd}}}\frac1{k^2}=\frac8{\pi d(1-\gamma)^2}\bigl(1+O(d^{-1})\bigr),\qquad w_\gamma(S_d)=\Theta_\gamma(d^{-1}).
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
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 4.5, p. 11

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_4_5 (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    (∀ m, uncertaintyLength γ (truncation (oddDegree m)) ≤
      ltwo (fun x => squareWave x-truncation (oddDegree m) x)^2/(1-γ)^2 ∧
      ltwo (fun x => squareWave x-truncation (oddDegree m) x)^2/(1-γ)^2 =
        16/(Real.pi*(1-γ)^2)*tailSquares (oddDegree m)) ∧
    Asymptotics.IsBigO atTop
      (fun m => (16/(Real.pi*(1-γ)^2)*tailSquares (oddDegree m)) /
        (8/(Real.pi*(oddDegree m:ℝ)*(1-γ)^2))-1)
      (fun m => 1/(oddDegree m:ℝ)) ∧
    Asymptotics.IsTheta atTop (fun m => window γ (truncation (oddDegree m)))
      (fun m => 1/(oddDegree m:ℝ)) := by sorry

end SpectralSharpness.NormalWindow.Supplement
