-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_4_4
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:16:10.1662+00:00
-- url     : https://prove2.me/theorems/30507959-932b-4122-95f3-d80f71d531c1
-- title:
--   Theorem 4.4 — Fejér costs exactly a factor two
-- statement:
--   For a positive odd integer d and 0<γ<1, compare the stated lower bounds for the uncertainty windows of S_d and σ_d. The factor two refers to these bounds, rather than an equality of the actual window widths.
--
--   Theorem 4.4 (Fejér costs exactly a factor two). σ_d has no overshoot (|σ_d| ≤ 1) and its
--   window lower bound is exactly twice that of S_d. Hence eliminating the Gibbs bend by a nonnegative
--   summability kernel is paid for, to the letter, by a halving of the achievable sharpness: σ_d′(0) = (1/2) S_d′(0).
--
--   $$
--   |\sigma_d(x)|\le1,\qquad \sigma_d'(0)=\tfrac12 S_d'(0),\qquad \frac{2\pi\gamma}{d+1}=2\frac{\pi\gamma}{d+1}.
--   $$
--
--   This statement supplies the source’s independent companion result alongside the published normal-window goal.
--
--   Differences from the source:
--   - encoding: odd positive integer d and d tending to infinity through odd integers → d=2m+1 with m a natural number tending to infinity; reason: this parametrizes exactly the permitted degrees, including d=1
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
--   - reading: the window lower bound is exactly twice and the slope is halved → both displayed bounds and the exact derivative identity, without an actual-window ratio equality; reason: the theorem and Figure 2 distinguish the bounds from actual window widths
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 4.4, p. 11

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_4_4 (m : ℕ) (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    (∀ x, |fejer (oddDegree m) x| ≤ 1) ∧
    window γ (truncation (oddDegree m)) ≥ Real.pi*γ/((oddDegree m:ℝ)+1) ∧
    window γ (fejer (oddDegree m)) ≥ 2*(Real.pi*γ/((oddDegree m:ℝ)+1)) ∧
    deriv (fejer (oddDegree m)) 0 = (1/2:ℝ)*deriv (truncation (oddDegree m)) 0 := by sorry

end SpectralSharpness.NormalWindow.Supplement
