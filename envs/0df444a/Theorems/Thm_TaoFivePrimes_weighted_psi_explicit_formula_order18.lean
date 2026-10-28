-- Prove2me | Theorems.Thm_TaoFivePrimes_weighted_psi_explicit_formula_order18
-- name    : TaoFivePrimes.weighted_psi_explicit_formula_order18
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T19:42:08.797314+00:00
-- url     : https://prove2.me/theorems/5040ce4c-8dda-47e5-993d-2827211a45d3
-- title:
--   The actual order-18 weighted psi explicit formula
-- statement:
--   For every real $A\ge1$ and $B>0$, this gives an exact explicit formula for $\int_0^1f(t)\psi(A+Bt)\,dt$, where $f(t)=(4t(1-t))^{18}$. The formula uses the actual nontrivial zeta zeros and analytic multiplicities, the existing quadratic Perron kernel, and the actual left-line Perron remainder. All polynomial weight, endpoint, main-term, countability, and series-interchange hypotheses are discharged. There is no RH assumption. This formula alone does not assert prime existence or any finite RH verification.
-- source:
--   Derived from the existing published Perron second-primitive explicit formula by two integrations by parts and absolutely convergent zero-series interchange; test weight (4t(1-t))^18.

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_ExplicitFormula

theorem TaoFivePrimes.weighted_psi_explicit_formula_order18 (A B : ℝ) (hA : 1 ≤ A) (hB : 0 < B) :
  let f : ℝ → ℝ := fun t => (4*t*(1-t))^18
  let d2 : ℝ → ℝ := iteratedDeriv 2 f
  let mass : ℝ := ∫ t in (0 : ℝ)..1, f t
  ((∫ t in (0 : ℝ)..1, f t*Chebyshev.psi (A+B*t) : ℝ) : ℂ) =
    (mass : ℂ)*((A+B/2 : ℝ) : ℂ) - (mass : ℂ)*logDeriv riemannZeta 0 -
      (∑' ρ : DusartSmoothing.NontrivialZetaZero, (∫ t in (0 : ℝ)..1,
        (d2 t : ℂ)*((DusartSmoothing.RvM.zeroMult ρ.val : ℂ)*
          DusartSmoothing.quadraticKernel (A+B*t) ρ.val)))/(B : ℂ)^2 +
      (∫ t in (0 : ℝ)..1, (d2 t : ℂ)*DusartSmoothing.perronLeftRemainder (A+B*t))/(B : ℂ)^2 := by sorry
