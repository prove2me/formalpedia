-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_4_2
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:08:41.831279+00:00
-- url     : https://prove2.me/theorems/7d6546af-bece-4cba-b70e-113a3b1751c4
-- title:
--   Theorem 4.2 — general uncertainty principle
-- statement:
--   Let f be an odd real trigonometric polynomial of positive integer degree bound d, with |f(x)|≤A everywhere and A>0. Let 0<γ<1. Write w_γ(f) for the length of the uncertainty component containing zero, including the full-circle case, and ♯_γ(f)=2γ/w_γ(f).
--
--   Theorem 4.2 (general uncertainty principle). Let f be an odd trigonometric polynomial of
--   degree ≤ d with ∥f∥∞ ≤ A. Then for every γ ∈ (0, 1),
--   w_γ(f) ≥ 2γ/(Ad).
--   Equivalently, writing ♯_γ(f) := 2γ/w_γ(f) for the effective sharpness,
--   ♯_γ(f) ≤ d · A.
--
--   $$
--   w_\gamma(f)\ge\frac{2\gamma}{Ad},\qquad\frac{2\gamma}{w_\gamma(f)}\le dA.
--   $$
--
--   Source defect retained: f(x)=sin(x)/10, d=1, A=1/10 and γ=1/2 give a full-circle window 2π<10. The bound has not been capped and no crossing hypothesis has been added.
--
--   Differences from the source:
--   - encoding: Theorem 4.2 gives degree at most d for a general odd trigonometric polynomial → an arbitrary natural degree bound d with 0<d; reason: oddness concerns f; the odd cutoff convention for the specific square-wave sums does not restrict the general degree bound
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
--   - encoding: the quotient 2γ/(Ad) → explicit A>0 and d>0 guards; reason: only undefined zero-amplitude or zero-degree denominators are excluded, not noncrossing classifiers
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 4.2, p. 10

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- Literal connected-component bound; false for the documented noncrossing example. -/
theorem theorem_4_2 (d : ℕ) (hd : 0 < d) (f : ℝ → ℝ) (A γ : ℝ)
    (hband : scalarBandLimited d f) (hodd : isOdd f)
    (hA : 0 < A) (hbound : ∀ x, |f x| ≤ A) (hγ : 0 < γ ∧ γ < 1) :
    window γ f ≥ 2*γ/(A*(d:ℝ)) ∧
    sharpness γ f ≤ (d:ℝ)*A ∧
    (window γ f ≥ 2*γ/(A*(d:ℝ)) ↔ sharpness γ f ≤ (d:ℝ)*A) := by sorry

end SpectralSharpness.NormalWindow.Supplement
