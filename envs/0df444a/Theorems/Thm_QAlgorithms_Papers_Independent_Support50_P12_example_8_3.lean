-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_example_8_3
-- name    : QAlgorithms.Papers.Independent.Support50.P12.example_8_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:53:25.629368+00:00
-- url     : https://prove2.me/theorems/bc36e5d2-138f-4552-a384-9e7bf75d25b3
-- title:
--   Example 8.3
-- statement:
--   Let $x\ge0$. All integrals below are Lebesgue integrals over $(0,\infty)$ of the displayed combined integrands.
--
--   The logarithmic and power generators satisfy
--
--   $$x\log x=\int_0^\infty\left(\frac{x}{1+t}-\frac{x}{x+t}\right)dt.$$
--
--   $$-x^\alpha=\frac{\sin(\alpha\pi)}\pi\int_0^\infty\frac{-x}{x+t}t^{\alpha-1}dt=-x+\frac{\sin(\alpha\pi)}\pi\int_0^\infty\left(\frac{x}{1+t}-\frac{x}{x+t}\right)t^{\alpha-1}dt\quad(0<\alpha<1).$$
--
--   $$x^\alpha=\frac{\sin((\alpha-1)\pi)}\pi\int_0^\infty\frac{x^2t^{\alpha-2}}{x+t}dt=\frac{\sin((\alpha-1)\pi)}\pi\int_0^\infty\left(\frac{x}{t}-\frac{x}{x+t}\right)t^{\alpha-1}dt$$
--
--   $$=x+\frac{\sin((\alpha-1)\pi)}\pi\int_0^\infty\left(\frac{x}{1+t}-\frac{x}{x+t}\right)t^{\alpha-1}dt\quad(1<\alpha<2).$$
--
--   The corresponding linear correction integrals equal $x$, and integrability of the displayed generator kernels is retained. These identify the densities of the representing measures and their full positive-half-line support.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 39, Example 8.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Example 8.3, PDF pp.39–40: natural-log and both power regimes, including
all converted representations and their integrability. The sin((a-1)pi) sign is retained. -/
theorem example_8_3 :
    (∀ x ≥ (0 : ℝ),
      IntegrableOn (fun t : ℝ => x / (1 + t) - x / (x + t)) (Ioi 0) ∧
      x * Real.log x = ∫ t in Ioi (0 : ℝ), x / (1 + t) - x / (x + t)) ∧
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ x ≥ (0 : ℝ),
      IntegrableOn (fun t : ℝ => -x / (x + t) * Real.rpow t (a - 1)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) (Ioi 0) ∧
      -Real.rpow x a = Real.sin (a * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), -x / (x + t) * Real.rpow t (a - 1) ∧
      Real.sin (a * Real.pi) / Real.pi *
        (∫ t in Ioi (0 : ℝ), x * Real.rpow t (a - 1) / (1 + t)) = x ∧
      -Real.rpow x a = -x + Real.sin (a * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) ∧
    (∀ a ∈ Ioo (1 : ℝ) 2, ∀ x ≥ (0 : ℝ),
      IntegrableOn (fun t : ℝ => x ^ 2 * Real.rpow t (a - 2) / (x + t)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (x / t - x / (x + t)) * Real.rpow t (a - 1)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) (Ioi 0) ∧
      Real.rpow x a = Real.sin ((a - 1) * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), x ^ 2 * Real.rpow t (a - 2) / (x + t) ∧
      Real.rpow x a = Real.sin ((a - 1) * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), (x / t - x / (x + t)) * Real.rpow t (a - 1) ∧
      Real.sin ((a - 1) * Real.pi) / Real.pi *
        (∫ t in Ioi (0 : ℝ), (x / t - x / (1 + t)) * Real.rpow t (a - 1)) = x ∧
      Real.rpow x a = x + Real.sin ((a - 1) * Real.pi) / Real.pi *
        ∫ t in Ioi (0 : ℝ), (x / (1 + t) - x / (x + t)) * Real.rpow t (a - 1)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
