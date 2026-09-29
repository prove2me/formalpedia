-- Prove2me | Theorems.Thm_SenTachyon_fieldStrength_gaugeTransform_eq_zero
-- name    : SenTachyon.fieldStrength_gaugeTransform_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:22:21.792869+00:00
-- url     : https://prove2.me/theorems/fade154a-1c1c-4adc-9046-a91249a4cb44
-- title:
--   Gauge transformations preserve vanishing field strength
-- statement:
--   Let $A=(A_1,A_2)$ be a $C^1$ gauge field on $\mathbb R^2$ with values in $2\times2$ complex matrices, and let $\Omega$ be a $C^2$ matrix-valued function with $\Omega(x)$ invertible for every $x$. If the field strength of $A$ vanishes identically, then so does the field strength of the gauge-transformed field:
--   $$F_{12}(A)\equiv 0\quad\Longrightarrow\quad F_{12}(\Omega\circ A)\equiv0,\qquad (\Omega\circ A)_\mu=\Omega A_\mu\Omega^{-1}-i(\partial_\mu\Omega)\Omega^{-1}.$$
--
--   In the paper this is applied with $\Omega=g^{-1}$ to the pure-gauge configuration $g\circ A_\mu=0$: returning to the original gauge produces a non-trivial gauge field whose field strength still vanishes.
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, p. 3, first paragraph ("This will give rise to a non-trivial gauge field configuration, but the field strength will continue to vanish")

import Mathlib
import Definitions.Def_SenTachyon_Defs

open scoped ContDiff
open Filter Topology

namespace SenTachyon
theorem fieldStrength_gaugeTransform_eq_zero (Ω : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (A : GaugeField)
    (hΩ : ∀ i j, ContDiff ℝ 2 (fun x => Ω x i j))
    (hA : ∀ μ i j, ContDiff ℝ 1 (fun x => A μ x i j))
    (hdet : ∀ x, IsUnit (Ω x).det)
    (hF : ∀ x, fieldStrength A x = 0) :
    ∀ x, fieldStrength (gaugeTransform Ω A) x = 0 := by sorry
end SenTachyon
