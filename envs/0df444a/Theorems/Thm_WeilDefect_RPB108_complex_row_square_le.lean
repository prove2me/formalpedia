-- Prove2me | Theorems.Thm_WeilDefect_RPB108_complex_row_square_le
-- name    : WeilDefect.RPB108.complex_row_square_le
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:27:37.713498+00:00
-- url     : https://prove2.me/theorems/b38b44d0-d910-4879-8416-98af072faa51
-- title:
--   Finite complex row bound from norm envelopes
-- statement:
--   Let $I$ be a finite type, $a,z:I\to\mathbb C$ and $b:I\to\mathbb R$. If $|a_i|\le b_i$ for every $i$, then
--
--   $$\left|\sum_i a_i z_i\right|^2\le\left(\sum_i b_i^2\right)\left(\sum_i|z_i|^2\right).$$
--
--   The entrywise envelope itself supplies the signs needed by the norm estimate; no extra nonnegativity assumption is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/NativePairing.lean#L5-L24; exact native theorem WeilDefect.RPB108.complex_row_square_le. SHA256 a7d507bfe099ea300b03c469d6f2fadf9c979d23799375364721dd2eb3c304c1. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.complex_row_square_le {ι : Type*} [Fintype ι]
    (a z : ι → ℂ) (b : ι → ℝ) (hb : ∀ i, ‖a i‖ ≤ b i) :
    ‖∑ i, a i*z i‖^2 ≤ (∑ i, (b i)^2)*(∑ i, ‖z i‖^2) := by sorry
