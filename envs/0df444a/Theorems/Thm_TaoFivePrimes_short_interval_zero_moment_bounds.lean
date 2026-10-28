-- Prove2me | Theorems.Thm_TaoFivePrimes_short_interval_zero_moment_bounds
-- name    : TaoFivePrimes.short_interval_zero_moment_bounds
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T19:28:05.11499+00:00
-- url     : https://prove2.me/theorems/fb00b472-9c51-443c-9229-fa3e28e9808a
-- title:
--   Absolute and finite-RH weighted nineteenth moments for short prime intervals
-- statement:
--   This package proves absolute nineteenth inverse-moment bounds for actual nontrivial zeta zeros, including convergence of the full series. For $H\ge10^8$ and $\log H\le22$, the absolute-height tail is at most $1/(2H^{18})$. It also proves, for $x\ge1$ and $10^8\le T\le H$, convergence and the weighted bound $$\sum_{|\gamma|>T}m(\rho)\frac{x^{\beta-1}}{|\gamma|^{19}}\le\frac{1}{2\sqrt{x}T^{18}}+\frac{1}{2H^{18}},$$ **conditional on finite RH through $H$**, which remains an explicit hypothesis. It does not assert that this finite RH verification has been performed.
-- source:
--   Positive nineteenth-moment bound from the proved zero-count increment estimate; conjugation reduction from PowerQuarterWeights; finite RH is an explicit hypothesis only in the weighted bound.

import Mathlib
import Definitions.Def_DusartTable1ZeroRanges_433_20261018
open ExplicitPNT.DusartTable1

theorem TaoFivePrimes.short_interval_zero_moment_bounds :
(
  ∀ (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22)
    (hγ : ∀ ρ ∈ Z, H < |ρ.im|),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/|ρ.im|^19)) ≤ 1/(2*H^18)
) ∧ (
  ∀ (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22),
    Summable (fun ρ : StrictHighAbsoluteZero H =>
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*(1/|ρ.val.im|^19)) ∧
    (∑' ρ : StrictHighAbsoluteZero H,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*(1/|ρ.val.im|^19)) ≤ 1/(2*H^18)
) ∧ (
  ∀ (x T H : ℝ) (hx : 1 ≤ x) (hT : (10 : ℝ)^8 ≤ T) (hTH : T ≤ H)
    (hlog : Real.log H ≤ 22)
    (hRH : ∀ ρ : ℂ, DusartSmoothing.RvM.IsNontrivialZero ρ → |ρ.im| ≤ H → ρ.re = 1/2),
    Summable (fun ρ : StrictHighAbsoluteZero T =>
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*x^(ρ.val.re-1)*(1/|ρ.val.im|^19)) ∧
    (∑' ρ : StrictHighAbsoluteZero T, (DusartSmoothing.RvM.zeroMult ρ.val : ℝ)*
      x^(ρ.val.re-1)*(1/|ρ.val.im|^19)) ≤ 1/(2*Real.sqrt x*T^18)+1/(2*H^18)
) := by sorry
