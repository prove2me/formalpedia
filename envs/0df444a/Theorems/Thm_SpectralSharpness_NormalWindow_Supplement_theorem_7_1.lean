-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_7_1
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:20:37.817129+00:00
-- url     : https://prove2.me/theorems/822df267-1b75-4452-9664-7c3c39e7defd
-- title:
--   Theorem 7.1 — spectrum of the two-layer ReLU NTK on the circle
-- statement:
--   Use the exact two-layer ReLU Gaussian NTK expectation with trainable input and output weights. Inputs on the circle are bias-augmented by 1; the separate unbiased kernel removes that coordinate. Define K from the expectation and λ_k from its cosine integral, with convolution normalization 1/(2π). The unbiased flow in the residual assertion is computed from that unbiased convolution operator and starts from zero output; its differential equation is also asserted.
--
--   Theorem 7.1 (spectrum of the two-layer ReLU NTK on the circle). Let K(τ) = Θ(x, x′)
--   for x = (cos a, sin a), x′ = (cos b, sin b) and τ = a − b. Then:
--   (a) K is even and 2π-periodic, and is given in closed form by
--   K(τ) = (1/π)(√(1 − ρ²) + ρ(π − arccos ρ)) + (1 + cos τ)(1/4 + (arcsin ρ)/(2π)), ρ = (1 + cos τ)/2.
--   (b) K is real-analytic on (0, π] and Lipschitz on T, with one-sided derivatives K′(0±) = ∓1/(√2 π). Thus
--   K has exactly one corner per period.
--   (c) The Fourier modes diagonalise Θ. The k-th eigenvalue is λ_k = (1/π) ∫_0^π K(τ) cos(kτ) dτ ≥ 0, and
--   λ_k = (1/(√2 π² k²))(1 + O(k^(−1))), k → ∞.
--   (d) The bias is not a detail. With the bias coordinate removed (w̃ = (w, 0), so ρ = cos τ) one has
--   λ_1 = 1/4 and λ_k = 0 for every odd k ≥ 3; consequently ∥H − f_t∥₂² ≥ 2π − 16/π = 1.190 . . . for
--   every t: an unbiased two-layer ReLU network in the NTK regime never learns H beyond its first
--   harmonic.
--
--   $$
--   \lambda_k=\frac1\pi\int_0^\pi K(\tau)\cos(k\tau)\,d\tau\ge0,\qquad \lambda_k=\frac1{\sqrt2\pi^2k^2}(1+O(k^{-1})),\qquad K'(0^\pm)=\mp\frac1{\sqrt2\pi}.
--   $$
--
--   This statement supplies the source’s independent companion result alongside the published normal-window goal.
--
--   Differences from the source:
--   - reading: §2 says normalized Lebesgue L², while the displayed identities and proofs use ‖sin(kx)‖₂²=π → ordinary Lebesgue L² on one period; reason: the proof fixes the displayed constants; the ordinary norm is √(2π) times the normalized norm
--   - encoding: O, o, Θ or Ω asymptotic notation → actual big-O, two-sided asymptotic bounds, limits or eventual inequalities at the stated filter; reason: quantifiers constrain the actual functions rather than an independent error term
--   - encoding: Gaussian expectations, circle Fourier eigenvalues and one corner per period → independent standard Gaussian weight coordinates, cosine integral eigenvalues, one-sided HasDerivWithinAt and differentiability exactly off period multiples; reason: no kernel spectrum or derivative bound is assumed
--   - encoding: the unbiased flow freezes all absent modes at zero initially → the residual is stated for the canonical zero-output operator-exponential flow, with its convolution differential equation also asserted; reason: the flow is computed from the source kernel and its zero initial data, rather than treated as an unrelated free function
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 7.1, pp. 17–18

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Kernel

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_7_1 :
    (∀ a b, tangentKernel true a b=circleKernel true (a-b)) ∧
    (∀ τ, circleKernel true (-τ)=circleKernel true τ) ∧
    Function.Periodic (circleKernel true) (2*Real.pi) ∧
    (∀ τ, circleKernel true τ=closedBiasedKernel τ) ∧
    (∀ τ ∈ Set.Ioc (0:ℝ) Real.pi, AnalyticAt ℝ (circleKernel true) τ) ∧
    (∃ C : ℝ≥0, LipschitzWith C (circleKernel true)) ∧
    HasDerivWithinAt (circleKernel true) (-1/(Real.sqrt 2*Real.pi)) (Set.Ici 0) 0 ∧
    HasDerivWithinAt (circleKernel true) (1/(Real.sqrt 2*Real.pi)) (Set.Iic 0) 0 ∧
    (∀ τ, DifferentiableAt ℝ (circleKernel true) τ ↔
      ¬ ∃ m : ℤ, τ=(m:ℝ)*(2*Real.pi)) ∧
    (∀ k x, kernelOperatorComplex true (fourierMode k) x =
      (eigenvalue true k:ℂ)*fourierMode k x) ∧
    (∀ k, 0 ≤ eigenvalue true k) ∧
    Asymptotics.IsBigO atTop
      (fun k : ℕ => eigenvalue true (k:ℤ)/(spectralConstant/(k:ℝ)^2)-1)
      (fun k : ℕ => 1/(k:ℝ)) ∧
    eigenvalue false 1=1/4 ∧
    (∀ k : ℕ, 3 ≤ k → Odd k → eigenvalue false (k:ℤ)=0) ∧
    IsKernelFlow false (zeroFlow false) ∧
    (∀ t, 0 ≤ t →
      2*Real.pi-16/Real.pi ≤ ltwo (fun x => squareWave x-zeroFlow false t x)^2) := by sorry

end SpectralSharpness.NormalWindow.Supplement
