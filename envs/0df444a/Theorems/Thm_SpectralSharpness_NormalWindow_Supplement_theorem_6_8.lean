-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_6_8
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:19:59.934014+00:00
-- url     : https://prove2.me/theorems/4143f456-b8bf-4366-9801-46372e9f2a24
-- title:
--   Theorem 6.8 — integration restores computability
-- statement:
--   For H=sgn(sin) and positive odd d, compare H−S_d with the difference of their periodic accumulators. The supremum is over one torus period and its endpoint attainment is evaluated using the periodic extension. Computability means real-input Type-2 computability, and the polynomial primitives form one uniformly computable family.
--
--   Theorem 6.8 (integration restores computability). For every odd d ≥ 1,
--   ∥H − S_d∥_{L∞} = 1, whereas sup_{x∈T} |(J H − J S_d)(x)| = (8/π) ∑_{k>d, k odd} 1/k² = (4/(πd)) (1 + O(1/d)) → 0 as d → ∞,
--   the supremum being attained at x = π. Consequently:
--   (a) J H is Turing-computable as a function: it is the uniform limit of the explicitly computable
--   trigonometric polynomials J S_d, with the effective error bound (4/(πd)) (1 + O(1/d));
--   (b) H is not computable (Theorem 5.1), although H = (d/dx) J H on T \ {0, π}. Thus (J H, H) is
--   an explicit instance of the general fact that differentiation is not a computable operator on
--   computable continuous functions [Pour-El and Richards 1989; Weihrauch 2000].
--
--   $$
--   \|H-S_d\|_\infty=1,\quad\sup_x|(JH-JS_d)(x)|=(JH-JS_d)(\pi)=\frac8\pi\sum_{\substack{k>d\\k\ \mathrm{odd}}}\frac1{k^2}=\frac4{\pi d}(1+O(d^{-1}))\to0.
--   $$
--
--   The effective uniform estimate is also stated directly as sup|JH−JS_d|≤4/(πd), using the reciprocal-square tail. The pair (JH,H) exhibits the source’s differentiation obstruction: the primitive is computable and continuous, its derivative equals H away from the jumps, and H is not a computable real function.
--
--   Differences from the source:
--   - encoding: odd positive integer d and d tending to infinity through odd integers → d=2m+1 with m a natural number tending to infinity; reason: this parametrizes exactly the permitted degrees, including d=1
--   - encoding: O, o, Θ or Ω asymptotic notation → actual big-O, two-sided asymptotic bounds, limits or eventual inequalities at the stated filter; reason: quantifiers constrain the actual functions rather than an independent error term
--   - encoding: functions and essential norms on the torus → periodic real representatives, extended-nonnegative essential norms and circle connected components measured on [−π,π); reason: this preserves ordinary length, including the full-circle width 2π and the identification of π with −π
--   - generalization: effective error (4/(πd))(1+O(1/d)) → the exact tail identity plus the direct upper bound 4/(πd); reason: the reciprocal-square integral comparison in the proof supplies this effective upper estimate
--   - encoding: computability of the primitive family and differentiation away from jumps → a single family oracle realizer and HasDerivAt off 0 and −π; reason: π and −π denote the same torus jump; no differentiability at either jump is asserted
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 6.8, p. 16

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Classification

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_6_8 :
    (∀ m, linfty (fun x => squareWave x-truncation (oddDegree m) x)=1 ∧
      sSup ((fun x => |accumulator squareWave x-accumulator (truncation (oddDegree m)) x|) '' torusInterval) =
        8/Real.pi*tailSquares (oddDegree m) ∧
      accumulator squareWave Real.pi-accumulator (truncation (oddDegree m)) Real.pi =
        8/Real.pi*tailSquares (oddDegree m) ∧
      (∀ x, |accumulator squareWave x-accumulator (truncation (oddDegree m)) x| ≤
        8/Real.pi*tailSquares (oddDegree m)) ∧
      8/Real.pi*tailSquares (oddDegree m) ≤ 4/(Real.pi*(oddDegree m:ℝ))) ∧
    Asymptotics.IsBigO atTop
      (fun m => (8/Real.pi*tailSquares (oddDegree m))/(4/(Real.pi*(oddDegree m:ℝ)))-1)
      (fun m => 1/(oddDegree m:ℝ)) ∧
    Tendsto (fun m => 8/Real.pi*tailSquares (oddDegree m)) atTop (nhds 0) ∧
    uniformComputableFamily torusInterval (fun m => accumulator (truncation (oddDegree m))) ∧
    TendstoUniformly (fun m => accumulator (truncation (oddDegree m))) (accumulator squareWave) atTop ∧
    typeTwoComputable torusInterval (accumulator squareWave) ∧
    Continuous (accumulator squareWave) ∧ ¬ typeTwoComputable torusInterval squareWave ∧
    (∀ x ∈ torusInterval, x ≠ 0 → x ≠ -Real.pi →
      HasDerivAt (accumulator squareWave) (squareWave x) x) := by sorry

end SpectralSharpness.NormalWindow.Supplement
