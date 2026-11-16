-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_7_9
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:23:22.296326+00:00
-- url     : https://prove2.me/theorems/f0acea63-3905-4e23-9ed8-22e3683a58ec
-- title:
--   Theorem 7.9 — time, not space, is the resource
-- statement:
--   Fix 0<γ<1 and the canonical zero-output biased circle NTK flow f_t from Theorem 7.2. The time statement ranges over every nonnegative time reaching the requested positive width w. A harmonic is fitted once its active-mode relative error is at most e^(−1), equivalently λ_kt≥1. Harmonic resources mean the least number fitted by a time reaching the requested width. Eventual reachability of positive widths is explicit, so the infimum never receives an empty set in the asymptotic claim.
--
--   Theorem 7.9 (time, not space, is the resource). In the NTK regime of Theorem 7.2, any training
--   procedure reaching w_γ(f_t) ≤ w must run for
--   t ≥ √2 π³ γ² w^(−2) (1 − o(1)) = Ω_γ(w^(−2)),
--   independently of the parameter count or the depth of the architecture. The number of harmonics
--   that must be fitted is only Θ(1/w); it is the time that is quadratic, because λ_k ≍ k^(−2) makes each
--   successive harmonic proportionally slower to fit.
--
--   $$
--   t\ge\sqrt2\pi^3\gamma^2w^{-2}(1-o(1))=\Omega_\gamma(w^{-2}),\qquad N_{\mathrm{required}}(w)=\Theta(w^{-1}).
--   $$
--
--   This statement supplies the source’s independent companion result alongside the published normal-window goal.
--
--   Differences from the source:
--   - encoding: O, o, Θ or Ω asymptotic notation → actual big-O, two-sided asymptotic bounds, limits or eventual inequalities at the stated filter; reason: quantifiers constrain the actual functions rather than an independent error term
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
--   - reading: the number of harmonics that must be fitted is only Θ(1/w) → the infimum of fitted active-harmonic counts over times achieving width at most w is Θ(1/w); reason: required resource means least required count; deliberate overtraining cannot have a uniform upper count
--   - encoding: independently of parameter count or depth in the NTK regime of Theorem 7.2 → the canonical zero-output flow of that fixed Gaussian convolution operator, with no architecture resource arguments; reason: does not extend the statement to unrelated kernels or nonlinear finite-network dynamics; the computed flow is shared with Theorem 7.2
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 7.9, p. 22

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Kernel

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- The lower bound is uniform over all times reaching a requested width; the harmonic
resource is the minimal number fitted by a time reaching it, not deliberate overtraining. -/
theorem theorem_7_9 (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    let f := zeroFlow true
    (∀ᶠ w in nhdsWithin (0:ℝ) (Set.Ioi 0), ∃ t, 0 ≤ t ∧ window γ (f t) ≤ w) ∧
    (∀ ε : ℝ, 0 < ε → ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w ∈ Set.Ioo 0 w₀,
      ∀ t, 0 ≤ t → window γ (f t) ≤ w →
        (Real.sqrt 2*Real.pi^3*γ^2-ε)/w^2 ≤ t) ∧
    (∃ c w₀ : ℝ, 0 < c ∧ 0 < w₀ ∧ ∀ w ∈ Set.Ioo 0 w₀,
      ∀ t, 0 ≤ t → window γ (f t) ≤ w → c/w^2 ≤ t) ∧
    Asymptotics.IsTheta (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (fun w => sInf {r : ℝ | ∃ t, 0 ≤ t ∧ window γ (f t) ≤ w ∧ r=fittedCount t})
      (fun w => 1/w) := by sorry

end SpectralSharpness.NormalWindow.Supplement
