-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_lemma_7_5
-- name    : SpectralSharpness.NormalWindow.Supplement.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:21:52.479211+00:00
-- url     : https://prove2.me/theorems/4303efd0-cc0b-4f3c-b818-4f05498012c5
-- title:
--   Lemma 7.5 — the rule halves the transition width
-- statement:
--   For every integer L≥0, define s₀(x)=clamp(x+1/2), s_{L+1}=clamp(2s_L−1/2) and s̃_L=2s_L−1. Here x ranges over the entire interval [−1,1], and 0<γ<1.
--
--   Lemma 7.5 (the rule halves the transition width). For every L ≥ 0, s̃_L is the affine-ramp
--   soft step
--   s̃_L(x) = −1, x ≤ −2^(−L−1);
--   s̃_L(x) = 2^(L+1)x, |x| < 2^(−L−1);
--   s̃_L(x) = +1, x ≥ 2^(−L−1),
--   hence w_γ(s̃_L) = γ 2^(−L).
--
--   $$
--   \widetilde s_L(x)=\begin{cases}-1&x\le-2^{-L-1},\\2^{L+1}x&|x|<2^{-L-1},\\1&x\ge2^{-L-1},\end{cases}\qquad w_\gamma(\widetilde s_L)=\gamma2^{-L}.
--   $$
--
--   This statement supplies the source’s supporting result for the associated companion theorem.
--
--   Differences from the source:
--   - encoding: L≥0, a ramp on [−1,1] and w_γ → a natural L and the ordinary length of the connected component within [−1,1]; reason: includes L=0 and keeps the interval window distinct from the torus window
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Lemma 7.5, p. 20

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Refinement

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem lemma_7_5 (L : ℕ) (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    (∀ x ∈ Set.Icc (-1:ℝ) 1,
      (x ≤ -(2:ℝ)^(-(L:ℤ)-1) → softStep L x= -1) ∧
      (|x| < (2:ℝ)^(-(L:ℤ)-1) → softStep L x=(2:ℝ)^(L+1)*x) ∧
      ((2:ℝ)^(-(L:ℤ)-1) ≤ x → softStep L x=1)) ∧
    intervalWindow γ (softStep L)=γ*(2:ℝ)^(-(L:ℤ)) := by sorry

end SpectralSharpness.NormalWindow.Supplement
