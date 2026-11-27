-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_Supplement_prop_30
-- name    : TFIMPhaseDiagram.Classical.Supplement.prop_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T21:04:58.711392+00:00
-- url     : https://prove2.me/theorems/1a359d84-1836-4a63-973e-623f17d9d53a
-- title:
--   Proposition 30 — Both quantitative absolute-field comparisons
-- statement:
--   Fix the supercritical parameters $b,\eta>0$ and take any $f\in L^2(S)$. Let $0\le a\le\|f\|_1\le z$ with $z\ge0$, and write $v=|\int_S f|$. Then
--   $$
--   \begin{aligned}
--   \Phi(|f|)-\Phi(f)&=\Lambda(|f|)-\Lambda(f)\\
--   &\ge\frac{\operatorname{sech}\eta}{2}(1-e^{v-\|f\|_1})(1-e^{-v-\|f\|_1})\\
--   &\ge\frac{\operatorname{sech}\eta\,e^{-z}(1-e^{-a})}{2}(\|f\|_1-v)\ge0.
--   \end{aligned}
--   $$
--   All norms and integrals use the normalized circle measure. The comparison applies to sign-changing fields as well as fields of one sign; it supplies the sign control needed in the full functional gap.
--
--   Differences from the source:
--   - encoding: |f| as a measurable L² equivalence class and sech(η) → the L² class of the pointwise real norm and 1/cosh(η); reason: these are the same functions and constants on every source instance
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026); pinned source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, pp. 17, Proposition 30

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement
attribute [local instance] Classical.propDecidable

/-- Proposition 30, p.17, with both quantitative lower bounds. -/
theorem prop_30 (b η : ℝ) (h : supercritical b η) (f : CircleL2)
    (a z : ℝ) (ha : 0 ≤ a) (hz : 0 ≤ z) (hl : a ≤ l1Norm f) (hu : l1Norm f ≤ z) :
    let absf : CircleL2 := (Lp.memLp f).norm.toLp (fun t => ‖f t‖)
    let v := |circleMean f|
    let B := (1 / Real.cosh η) / 2 *
      (1-Real.exp (v-l1Norm f)) * (1-Real.exp (-v-l1Norm f))
    let C := (1 / Real.cosh η) * Real.exp (-z) * (1-Real.exp (-a)) / 2 * (l1Norm f-v)
    phi b η absf - phi b η f = cumulant η absf - cumulant η f ∧
    B ≤ phi b η absf - phi b η f ∧ C ≤ B ∧ 0 ≤ C := by sorry

end TFIMPhaseDiagram.Classical.Supplement
