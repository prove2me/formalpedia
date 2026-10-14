-- Prove2me | Theorems.Thm_WeilDefect_RPB108_native_row_square_of_energy_floor
-- name    : WeilDefect.RPB108.native_row_square_of_energy_floor
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:26:47.886461+00:00
-- url     : https://prove2.me/theorems/155ea419-315d-447d-af9a-0ea372d6ba81
-- title:
--   Finite row bound against actual energy
-- statement:
--   Let $I$ be a finite type, $a,z:I\to\mathbb C$ and $b:I\to\mathbb R$. Let $g,d,U\in\mathbb R$. Assume $|a_i|\le b_i$, $d\ge0$, $\sum_i b_i^2\le dg$, and $g\sum_i|z_i|^2\le U$. Then
--
--   $$\left|\sum_i a_i z_i\right|^2\le dU.$$
--
--   A checked scalar budget and supplied energy floor imply the row-square estimate. Neither positivity of $g$ nor nonnegativity of $U$ is added as a premise.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/NativePairing.lean#L26-L40; exact native theorem WeilDefect.RPB108.native_row_square_of_energy_floor. SHA256 a7d507bfe099ea300b03c469d6f2fadf9c979d23799375364721dd2eb3c304c1. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.native_row_square_of_energy_floor {ι : Type*} [Fintype ι]
    (a z : ι → ℂ) (b : ι → ℝ) (g d V : ℝ)
    (hb : ∀ i, ‖a i‖ ≤ b i) (hd : 0 ≤ d)
    (hbudget : (∑ i, (b i)^2) ≤ d*g)
    (hfloor : g*(∑ i, ‖z i‖^2) ≤ V) :
    ‖∑ i, a i*z i‖^2 ≤ d*V := by sorry
