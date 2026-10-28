-- Prove2me | Theorems.Thm_RHInBoxAnalytic_rect_winding_generic
-- name    : RHInBoxAnalytic.rect_winding_generic
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:33:13.121237+00:00
-- url     : https://prove2.me/theorems/1d04bf57-b7ff-4a07-ab5e-e8af6227a5f8
-- title:
--   Winding of one pole around a rectangle
-- statement:
--   Let $\rho$ lie strictly inside the complex rectangle
--   $R=[\sigma_0,\sigma_1]\times[T_0,T_1]$. The positively oriented four-side integral is
--   $$\int_{\partial R}\frac{dz}{z-\rho}=2\pi i.$$
--   This is the unit-winding calculation used by the rectangle zero-count proof.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_zero_localization/lean/RHInBoxAnalytic.lean#L124-L225

import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Mathlib
/- Task 2 (parameterized RH-in-a-box): generalize the zeta Blaschke split + box argument
   principle from the merged FIXED ball `ball cB 13` / fixed corners to an ARBITRARY box
   `[sigma0, sigma1] x [T0, T1]` with a VARIABLE Blaschke ball `(c, R)`, the geometry entering
   only as hypotheses `hRpos`, `hbox_ball`, `hs1` (and the box-ordering `hsig`, `hT`).

   This file reproduces, over variable corners and a variable ball, the three merged atoms
     - the per-pole interior winding `Bd((z-ρ)^{-1}) = 2*pi*I` (branch-split primitive),
     - the residue-sum linearity `Bd(∑ d/(z-ρ)) = 2*pi*I*∑ d`,
     - the analytic E-arg-principle `Bd(E) = 0` (Mathlib `integral_boundary_rect_eq_zero...`),
   and the KERNEL-DERIVED local Blaschke split of `logDeriv riemannZeta` over the variable ball
   (`MeromorphicOn.extract_zeros_poles`, E-holomorphicity in-kernel), then composes them into
     `RHInBoxAnalytic.zeta_count_eq_winding_generic`:
   the actual divisor of `riemannZeta` over `ball c R` is nonneg, captures every box zero, and its
   total equals the Arb winding integer `N` (derived from `hwind` via the argument principle).

   Divisor-support finiteness is obtained from `IsCompact.inter_riemannZetaZeros_finite`
   (compact `closedBall c R` meets `riemannZetaZeros` finitely), NOT from meromorphy on the closed
   ball -- so no assumption is needed about the pole `1` on the closed-ball boundary; only
   `1 ∉ ball c R` (open) enters, exactly as the brief requires.

   conjecture1_proved = False.  This is a kernel derivation of a parameterized argument-principle
   count; it does NOT prove RH. -/


open Complex Filter MeasureTheory Real
open scoped Topology

section
namespace RHInBoxAnalytic
end RHInBoxAnalytic
open RHInBoxAnalytic

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.
    (Verbatim from the merged `BlaschkeBox.lean`; pure Mathlib, function-agnostic.) -/







/-! ## Part B: log-derivative of the factorized-rational product.  (Verbatim.) -/





/-! ## Part C: `riemannZeta` meromorphic-order facts on `{1}ᶜ`.  (Verbatim from merged.) -/



/-! ## Part D: generic per-pole interior winding and residue-sum atoms over variable corners.

    Generalizes `WindingCount.winding_lambda_five_rect_winding` and
    `BoxArgPrinciple.box_residue_sum_lambda` from the fixed corners `2/5,3/5,10,35` to variable
    `sigma0 < ρ.re < sigma1`, `T0 < ρ.im < T1`. -/

theorem RHInBoxAnalytic.rect_winding_generic
    (sigma0 sigma1 T0 T1 : ℝ) (ρ : ℂ)
    (hre0 : sigma0 < ρ.re) (hre1 : ρ.re < sigma1)
    (him0 : T0 < ρ.im) (him1 : ρ.im < T1) :
    (∫ x in sigma0..sigma1, ((↑x + (T0 : ℂ) * I) - ρ)⁻¹)
        - (∫ x in sigma0..sigma1, ((↑x + (T1 : ℂ) * I) - ρ)⁻¹)
        + I • (∫ y in T0..T1, (((sigma1 : ℂ) + ↑y * I) - ρ)⁻¹)
        - I • (∫ y in T0..T1, (((sigma0 : ℂ) + ↑y * I) - ρ)⁻¹)
      = 2 * ↑π * I := by sorry
