-- Prove2me | Theorems.Thm_RHInBoxAnalytic_zeta_blaschke_split_ball
-- name    : RHInBoxAnalytic.zeta_blaschke_split_ball
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:33:14.783252+00:00
-- url     : https://prove2.me/theorems/ba1fc421-ee43-4489-8368-c0f3b0e0ca84
-- title:
--   Zeta logarithmic-derivative decomposition in a ball
-- statement:
--   Let $R>0$, and suppose a closed rectangle lies inside $B(c,R)$ while $1$ lies
--   outside that open ball. There is a function $E$ differentiable on the rectangle
--   such that the ball's finite zeta-zero support contains every zeta zero in the ball,
--   each listed divisor multiplicity is at least one, and at every nonzero point of
--   zeta in the ball,
--   $$\operatorname{logDeriv}\zeta(z)
--   =\sum_{\rho}\frac{\operatorname{ord}_{\rho}(\zeta)}{z-\rho}+E(z).$$
--   The sum is over the defined finite zero support in $B(c,R)$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_zero_localization/lean/RHInBoxAnalytic.lean#L318-L475

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











/-! ## Part E: variable-ball local Blaschke split of `logDeriv riemannZeta`.

    Generalizes `BlaschkeBox.zeta_blaschke_split_box` to an arbitrary ball `(c, R)` whose interior
    avoids `1` (`hs1`) and whose box `[σ0,σ1]x[T0,T1] ⊆ ball c R` (`hbox_ball`).  Divisor
    finiteness comes from `IsCompact.inter_riemannZetaZeros_finite`. -/

theorem RHInBoxAnalytic.zeta_blaschke_split_ball
    (sigma0 sigma1 T0 T1 : ℝ) (c : ℂ) (R : ℝ)
    (hRpos : 0 < R)
    (hbox_ball : ∀ ρ : ℂ, (sigma0 ≤ ρ.re ∧ ρ.re ≤ sigma1) → (T0 ≤ ρ.im ∧ ρ.im ≤ T1) →
      ρ ∈ Metric.ball c R)
    (hs1 : (1 : ℂ) ∉ Metric.ball c R) :
    ∃ (E : ℂ → ℂ),
      DifferentiableOn ℂ E (Set.Icc sigma0 sigma1 ×ℂ Set.Icc T0 T1) ∧
      (∀ ρ ∈ zeroFinset c R hs1,
        (1 : ℤ) ≤ (MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ) ∧
      (∀ ρ ∈ Metric.ball c R, riemannZeta ρ = 0 → ρ ∈ zeroFinset c R hs1) ∧
      (∀ z ∈ Metric.ball c R, riemannZeta z ≠ 0 →
        logDeriv riemannZeta z = (∑ ρ ∈ zeroFinset c R hs1,
          ((MeromorphicOn.divisor riemannZeta (Metric.ball c R) : ℂ → ℤ) ρ : ℂ) / (z - ρ)) + E z) := by sorry
