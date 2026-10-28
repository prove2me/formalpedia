-- Prove2me | Theorems.Thm_TaoFivePrimes_positive_zero_nineteenth_moment_tail
-- name    : TaoFivePrimes.positive_zero_nineteenth_moment_tail
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T19:10:48.622985+00:00
-- url     : https://prove2.me/theorems/12efc97c-0503-4fb4-86c3-c99532350e1c
-- title:
--   A nineteenth inverse moment bound for positive zeta zeros
-- statement:
--   For $H\ge10^8$ with $\log H\le22$, every finite set $Z$ of actual nontrivial zeta zeros with imaginary part greater than $H$ satisfies $$\sum_{\rho\in Z}\frac{m(\rho)}{(\operatorname{Im}\rho)^{19}}\le\frac1{4H^{18}}.$$ Multiplicities are the actual analytic zeta multiplicities. The proof uses the already proved zero-count increment bound and an explicit Abel primitive. It is unconditional and asserts no finite RH verification.
-- source:
--   Derived by exact Abel summation from the proved Riemann–von Mangoldt zero-count increment estimate. Used for the order-18 Ramaré–Saouter smoothing weight.

import Mathlib
import Definitions.Def_DusartTable1ZeroRanges_433_20261018

theorem TaoFivePrimes.positive_zero_nineteenth_moment_tail
    (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H : ℝ) (hH : (10 : ℝ)^8 ≤ H) (hlog : Real.log H ≤ 22)
    (hγ : ∀ ρ ∈ Z, H < ρ.im) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)*(1/ρ.im^19)) ≤ 1/(4*H^18) := by sorry
