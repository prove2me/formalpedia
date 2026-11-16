-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_8_2
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:23:52.068596+00:00
-- url     : https://prove2.me/theorems/28f57c60-c01d-4774-a9fc-04c19daf7b7d
-- title:
--   Theorem 8.2
-- statement:
--   Fix an arbitrary real 0<γ<1. Use the exact printed degree ceiling, the literal finite sum S_d and the total threshold decision map, with ties |S_d|=γ counted as decisions. Probabilities below are supported on the torus and have only an upper density bound relative to ordinary length. No computability assumption on γ, lower density bound or partial decision convention is inserted.
--
--   Theorem 8.2. Let γ ∈ (0, 1).
--   (a) For every ε > 0 there is an (ε, γ)-confident classifier of bandwidth d = ⌈8/(πε(1 − γ)²)⌉, namely (S_d, c),
--   and it is Turing-computable. Its abstention region is exactly U_γ(S_d) and has measure Θ_γ(1/d).
--   (b) There is no (0, γ)-confident classifier with f continuous; in particular none with f computable.
--   (Indeed |E| ≥ w_γ(f) ≥ 2γ/(Ad) > 0 for every band-limited f, by Theorem 4.2. For general continuous
--   f, {|f| < γ} contains a neighbourhood of 0 after symmetrisation, hence has positive measure.)
--   (c) For a distribution D on T with density bounded by ρ, the abstention rate obeys
--   2γρ/(Ad) ≤ D(U_γ(f)) ≤ (8ρ/(πd(1 − γ)²))(1 + O(1/d))
--   for f = S_d, and D(U_γ(f)) ≥ 2γρ/(Ad) for every band-limited f.
--
--   $$
--   d=\left\lceil\frac8{\pi\varepsilon(1-\gamma)^2}\right\rceil,\qquad \frac{2\gamma\rho}{Ad}\le D(U_\gamma(S_d))\le\frac{8\rho}{\pi d(1-\gamma)^2}(1+O(d^{-1})).
--   $$
--
--   Source defects retained: a density upper bound gives no positive lower mass on the uncertain set, and a nonconstant total discrete decision map on the connected torus is not Type-2 computable. The degree ceiling may be even. None of these claims is silently corrected.
--
--   The uncertainty-size rate is asserted along the actual ceiling-degree family as ε tends to zero, including even cutoffs, as well as along the positive odd sequence used elsewhere in the paper.
--
--   Differences from the source:
--   - encoding: odd positive integer d and d tending to infinity through odd integers → d=2m+1 with m a natural number tending to infinity; reason: this parametrizes exactly the permitted degrees, including d=1
--   - encoding: O, o, Θ or Ω asymptotic notation → actual big-O, two-sided asymptotic bounds, limits or eventual inequalities at the stated filter; reason: quantifiers constrain the actual functions rather than an independent error term
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
--   - encoding: the exact ceiling bandwidth, abstention ties and upper density bound → the literal ceiling, the finite sum for either parity, total three-label realizers, and a probability with density at most ρ; reason: preserves the odd-degree conflict and the false lower-probability/total-computability claims
--   - generalization: the distributional upper bound with 1+O(1/d) → the exact reciprocal-square-tail upper bound and its constrained relative big-O remainder; reason: the source proof integrates Theorem 4.5 and therefore supplies this stronger quantitative witness
--   - encoding: all approximants in §2 are odd and the probability lower bound uses 2γ/(Ad) → the general approximant has explicit oddness and positive degree/amplitude guards; reason: the standing symmetry condition is retained and only undefined denominators are excluded
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 8.2, p. 24

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Classification

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- Literal theorem, including the documented false total-computability and density lower claims. -/
theorem theorem_8_2 (γ : ℝ) (hγ : 0 < γ ∧ γ < 1) :
    (∀ ε : ℝ, 0 < ε →
      let d := confidenceDegree ε γ
      Confident ε γ (truncation d) (thresholdDecision γ (truncation d)) ∧
      scalarBandLimited d (truncation d) ∧
      typeTwoComputable torusInterval (truncation d) ∧
      discreteComputable torusInterval (thresholdDecision γ (truncation d)) ∧
      {x ∈ torusInterval | thresholdDecision γ (truncation d) x=2}=uncertainty γ (truncation d)) ∧
    Asymptotics.IsTheta (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (fun ε => uncertaintyLength γ (truncation (confidenceDegree ε γ)))
      (fun ε => 1/(confidenceDegree ε γ:ℝ)) ∧
    Asymptotics.IsTheta atTop (fun m => uncertaintyLength γ (truncation (oddDegree m)))
      (fun m => 1/(oddDegree m:ℝ)) ∧
    (¬ ∃ (f : ℝ → ℝ) (c : ℝ → Fin 3), ContinuousOn f torusInterval ∧ Confident 0 γ f c) ∧
    (¬ ∃ (f : ℝ → ℝ) (c : ℝ → Fin 3), typeTwoComputable torusInterval f ∧ Confident 0 γ f c) ∧
    (∀ (D : Measure ℝ) (ρ : ℝ), UpperDensityBound D ρ →
      (∀ m, let d := oddDegree m
        ENNReal.ofReal (2*γ*ρ/(supNorm (truncation d)*(d:ℝ))) ≤ D (uncertainty γ (truncation d)) ∧
        D (uncertainty γ (truncation d)) ≤
          ENNReal.ofReal (16*ρ/(Real.pi*(1-γ)^2)*tailSquares d)) ∧
      (∀ (d : ℕ) (hd : 0 < d) (f : ℝ → ℝ) (A : ℝ), 0 < A →
        scalarBandLimited d f → isOdd f → (∀ x, |f x| ≤ A) →
        ENNReal.ofReal (2*γ*ρ/(A*(d:ℝ))) ≤ D (uncertainty γ f))) ∧
    Asymptotics.IsBigO atTop
      (fun m => (2*(oddDegree m:ℝ)*tailSquares (oddDegree m))-1)
      (fun m => 1/(oddDegree m:ℝ)) := by sorry

end SpectralSharpness.NormalWindow.Supplement
