-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_D_3
-- name    : TwoItemMenu1393.Main.lemma_D_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:44.496961+00:00
-- url     : https://prove2.me/theorems/5163ecdb-f88f-4240-b447-6aa5f0e72f2f
-- title:
--   Lemma D.3 — Integral rigidity of the allocation field
-- statement:
--   There is an absolute positive constant $C$ such that every rhombus of full hexagonal cells and every admissible competing mechanism satisfies
--   $$\int_{\mathrm{rhombus}}\|\mathcal T(D\Gamma_h(v))\|\,dv\le CE.$$
--   Here $\Gamma_h$ is the affine interpolation of the competitor's actual upper-left-vertex allocations, $\mathcal T(J)=(J_{12},J_{21},J_{11}-J_{22})$, and $E$ sums all six supporting-plane gaps at every rhombus center as in (22). The norm of $\mathcal T$ is Euclidean, integration uses planar Lebesgue area, and $C$ is independent of scale, rhombus and mechanism. This is the quantitative no-shear estimate for the lower-bound family.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: the trianglewise Jacobian → the explicit interpolation matrix, set to zero on triangle boundaries; reason: boundaries have zero planar area; the integral and its norm are unchanged
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma D.3, p. 29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=29

import Definitions.Def_TwoItemMenu1393_Main_Fields
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma D.3, p. 29.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_D_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ) (z : Vec) (m : ℕ) (M : Mechanism),
      FullRhombus h z m → Admissible M →
      (∫ v in rhombusRegion h z m, ‖scalarDeviation (fieldDerivative h M v)‖) ≤
        C * totalDefect h M z m := by sorry

end TwoItemMenu1393.Main
