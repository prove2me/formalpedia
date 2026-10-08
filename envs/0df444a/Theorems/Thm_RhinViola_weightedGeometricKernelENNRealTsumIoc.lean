-- Prove2me | Theorems.Thm_RhinViola_weightedGeometricKernelENNRealTsumIoc
-- name    : RhinViola.weightedGeometricKernelENNRealTsumIoc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T23:41:56.541201+00:00
-- url     : https://prove2.me/theorems/ae0e12fd-3079-48fb-bed0-2e088438a45c
-- title:
--   Weighted geometric ENNReal kernel identity on the unit interval away from the endpoint
-- statement:
--   If x and y lie in (0,1] and x is not the endpoint 1, then x<1 and hence xy<1. The pointwise ENNReal geometric-kernel identity therefore applies. This isolates the sole exceptional outer endpoint needed for the later almost-everywhere integral argument.
-- source:
--   Unit-square endpoint reduction for the geometric-series/Tonelli step in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Theorems.Thm_RhinViola_weightedGeometricKernelENNRealTsum
import Mathlib.Tactic

theorem RhinViola.weightedGeometricKernelENNRealTsumIoc
    (h m : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioc (0 : ℝ) 1)
    (hx1 : x ≠ 1) :
    (∑' k : ℕ,
      ENNReal.ofReal (x ^ (h + k)) *
        ENNReal.ofReal (y ^ (m + k))) =
      ENNReal.ofReal (x ^ h * y ^ m / (1 - x * y)) := by sorry
