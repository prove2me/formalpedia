-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_6_4
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:18:43.179812+00:00
-- url     : https://prove2.me/theorems/443d7111-f324-44e2-a9c5-ad789b58bb16
-- title:
--   Theorem 6.4 — balance law for the truncated classifier
-- statement:
--   Fix 0<γ<1. Let t_γ be the unique inverse value of Φ on (0,π), and let w_γ(S_d) be the uncertainty component length at zero for positive odd d. All three asymptotic identities are retained.
--
--   Theorem 6.4 (balance law for the truncated classifier). For every γ ∈ (0, 1), as d → ∞
--   through odd values,
--   w_γ(S_d) = (2t_γ/(d + 1)) (1 + o(1)) and S_d′(0) · w_γ(S_d) → 4t_γ/π.
--   Consequently the exact constant in Theorem 4.3 is 2t_γ/(πγ):
--   w_γ(S_d) = (2t_γ/(πγ)) · (πγ/(d + 1)) (1 + o(1)).
--
--   $$
--   w_\gamma(S_d)=\frac{2t_\gamma}{d+1}(1+o(1)),\quad S_d'(0)w_\gamma(S_d)\to\frac{4t_\gamma}\pi,\quad\frac{w_\gamma(S_d)}{\pi\gamma/(d+1)}\to\frac{2t_\gamma}{\pi\gamma}.
--   $$
--
--   This statement supplies the source’s independent companion result alongside the published normal-window goal.
--
--   Differences from the source:
--   - encoding: odd positive integer d and d tending to infinity through odd integers → d=2m+1 with m a natural number tending to infinity; reason: this parametrizes exactly the permitted degrees, including d=1
--   - encoding: O, o, Θ or Ω asymptotic notation → actual big-O, two-sided asymptotic bounds, limits or eventual inequalities at the stated filter; reason: quantifiers constrain the actual functions rather than an independent error term
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 6.4, p. 14

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_6_4 (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    Tendsto (fun m => window γ (truncation (oddDegree m)) /
      (2*gibbsInverse γ/((oddDegree m:ℝ)+1))) atTop (nhds 1) ∧
    Tendsto (fun m => deriv (truncation (oddDegree m)) 0 *
      window γ (truncation (oddDegree m))) atTop (nhds (4*gibbsInverse γ/Real.pi)) ∧
    Tendsto (fun m => window γ (truncation (oddDegree m)) /
      (Real.pi*γ/((oddDegree m:ℝ)+1))) atTop (nhds (2*gibbsInverse γ/(Real.pi*γ))) := by sorry

end SpectralSharpness.NormalWindow.Supplement
