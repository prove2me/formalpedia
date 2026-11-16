-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_7_2
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:21:10.297197+00:00
-- url     : https://prove2.me/theorems/e82f15f1-825f-498d-bb20-61228641c5c8
-- title:
--   Theorem 7.2 — spectral cutoff in the NTK regime
-- statement:
--   Let f_t be the canonical zero-output flow computed from the actual biased circle convolution operator with target H=sgn(sin). Absolute convergence of its operator-exponential series and its classical gradient-flow equation are conclusions, together with the usual continuous periodic evolution properties. No regularity, spectral solution or derivative bound is assumed. Put α=1/(√2π²) and d(t)=√(αt). Relative mode errors are asserted only on active modes, where the target coefficient is nonzero. All five printed clauses follow the spectral identity.
--
--   Theorem 7.2 (spectral cutoff in the NTK regime). Let f_t be the NTK gradient flow with
--   target H on T, started at f_0 ≡ 0. Then f_t is odd with f_t(0) = 0 and
--   f̂_t(k) = (1 − e^(−λ_k t)) Ĥ(k), k ∈ Z.
--   Put α = 1/(√2 π²) and d(t) := √(αt). Then, as t → ∞:
--   (a) Low frequencies converge first. The relative mode error
--   |Ĥ(k) − f̂_t(k)|/|Ĥ(k)| = e^(−λ_k t)
--   is at most e^(−1) exactly for |k| ≤ d(t)(1 + o(1)): the fitted bandwidth grows as √t and the modes
--   are fitted in increasing order.
--   (b) High-frequency residue Θ(1/d).
--   ∥H − f_t∥₂² = (16/π) ∑_{k>0, k odd} e^(−2λ_k t)/k² = (4/√(2π)) (1/d(t)) (1 + o(1)) = (4√π/2^(1/4)) t^(−1/2) (1 + o(1)).
--   (c) The hard truncation is the right idealisation. ∥f_t − S_{d(t)}∥₂² = Θ(1/d(t)).
--   (d) Sharpness. ∥f_t′∥∞ ≤ (2/√π) d(t)(1 + o(1)) and therefore w_γ(f_t) ≥ (√π γ/d(t))(1 − o(1)).
--   (e) Time, not space. Reaching w_γ(f_t) ≤ w requires t = Ω_γ(w^(−2)).
--
--   $$
--   \widehat f_t(k)=(1-e^{-\lambda_kt})\widehat H(k),\quad\|H-f_t\|_2^2=\frac4{\sqrt{2\pi}\,d(t)}(1+o(1))=\frac{4\sqrt\pi}{2^{1/4}}t^{-1/2}(1+o(1)),\quad w_\gamma(f_t)\ge\frac{\sqrt\pi\gamma}{d(t)}(1-o(1)).
--   $$
--
--   The hard-truncation comparison also retains the positive finite integral from the proof: d(t)‖f_t−S_{d(t)}‖₂² tends to (8/π)∫₀^∞[(1−e^(−1/s²))−1_{s≤1}]²s^(−2)ds. This uses the actual soft-versus-hard difference rather than the proof’s mistaken indicator replacement.
--
--   Differences from the source:
--   - reading: §2 says normalized Lebesgue L², while the displayed identities and proofs use ‖sin(kx)‖₂²=π → ordinary Lebesgue L² on one period; reason: the proof fixes the displayed constants; the ordinary norm is √(2π) times the normalized norm
--   - encoding: O, o, Θ or Ω asymptotic notation → actual big-O, two-sided asymptotic bounds, limits or eventual inequalities at the stated filter; reason: quantifiers constrain the actual functions rather than an independent error term
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
--   - encoding: zero-output NTK gradient flow → the canonical operator-exponential series built from the actual convolution operator, with absolute convergence and the classical flow equation asserted as conclusions; reason: computes the source flow from its kernel and initial data without adding a regularity hypothesis or prescribing its Fourier multipliers
--   - encoding: relative mode errors and d(t) truncation → relative errors only on nonzero target coefficients and the finite sum over odd k≤floor(d(t)); reason: avoids a 0/0 quotient and preserves the real cutoff
--   - generalization: Θ(1/d(t)) soft-versus-hard error → also the positive finite integral and its leading rescaled limit from the proof; reason: retains the leading quantitative witness explicitly required by the brief
--   - encoding: the derivative supremum norm → differentiability and boundedness of the derivative image are explicit conclusions; reason: prevents a real supremum from defaulting to zero on an unbounded derivative
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 7.2, pp. 18–19

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Kernel

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_7_2 :
    let f := zeroFlow true
    (∀ t, 0 ≤ t → ∀ x, Summable (fun n => |flowSeriesTerm true t x n|)) ∧
    IsKernelFlow true f ∧
    (∀ t, 0 ≤ t → isOdd (f t) ∧ f t 0=0 ∧
      ∀ k, fourier (f t) k=(1-Complex.exp (-(eigenvalue true k:ℂ)*(t:ℂ)))*fourier squareWave k) ∧
    (∀ t, 0 ≤ t → ∀ k, activeMode k →
      ‖fourier squareWave k-fourier (f t) k‖ / ‖fourier squareWave k‖ =
        Real.exp (-eigenvalue true k*t)) ∧
    (∃ cutoff : ℝ → ℝ, Tendsto (fun t => cutoff t/fittedBandwidth t) atTop (nhds 1) ∧
      ∀ᶠ t in atTop, ∀ k, activeMode k →
        (Real.exp (-eigenvalue true k*t) ≤ Real.exp (-1) ↔ |(k:ℝ)| ≤ cutoff t)) ∧
    (∀ k l : ℤ, activeMode k → activeMode l → |k| ≤ |l| →
      ∀ t, 0 ≤ t → Real.exp (-eigenvalue true k*t) ≤ Real.exp (-eigenvalue true l*t)) ∧
    (∀ t, 0 ≤ t → ltwo (fun x => squareWave x-f t x)^2 = 16/Real.pi *
      ∑' k : ℕ, if 0 < k ∧ Odd k then Real.exp (-2*eigenvalue true (k:ℤ)*t)/(k:ℝ)^2 else 0) ∧
    Tendsto (fun t => fittedBandwidth t*ltwo (fun x => squareWave x-f t x)^2)
      atTop (nhds (4/Real.sqrt (2*Real.pi))) ∧
    Tendsto (fun t => Real.sqrt t*ltwo (fun x => squareWave x-f t x)^2)
      atTop (nhds (4*Real.sqrt Real.pi/Real.rpow 2 (1/4))) ∧
    0 < softHardIntegral ∧ IntegrableOn
      (fun s : ℝ => ((1-Real.exp (-1/s^2))-(if s ≤ 1 then 1 else 0))^2/s^2) (Set.Ioi 0) ∧
    Tendsto (fun t => fittedBandwidth t*
      ltwo (fun x => f t x-truncationReal (fittedBandwidth t) x)^2)
      atTop (nhds (8/Real.pi*softHardIntegral)) ∧
    Asymptotics.IsTheta atTop
      (fun t => ltwo (fun x => f t x-truncationReal (fittedBandwidth t) x)^2)
      (fun t => 1/fittedBandwidth t) ∧
    (∀ t, 0 < t → Differentiable ℝ (f t) ∧ BddAbove (Set.range fun x => |deriv (f t) x|)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop,
      supNorm (deriv (f t)) ≤ (2/Real.sqrt Real.pi+ε)*fittedBandwidth t) ∧
    (∀ γ : ℝ, 0 < γ ∧ γ < 1 →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop,
        (Real.sqrt Real.pi*γ-ε)/fittedBandwidth t ≤ window γ (f t)) ∧
      ∃ c w₀ : ℝ, 0 < c ∧ 0 < w₀ ∧ ∀ w ∈ Set.Ioo 0 w₀, ∀ t, 0 ≤ t →
        window γ (f t) ≤ w → c/w^2 ≤ t) := by sorry

end SpectralSharpness.NormalWindow.Supplement
