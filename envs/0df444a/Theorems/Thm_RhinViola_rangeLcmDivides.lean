-- Prove2me | Theorems.Thm_RhinViola_rangeLcmDivides
-- name    : RhinViola.rangeLcmDivides
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:34:57.967665+00:00
-- url     : https://prove2.me/theorems/a5a35ff5-2c78-41e5-a39d-5858a2785a00
-- title:
--   Every positive integer up to n divides the range lcm
-- statement:
--   Define d_n as the least common multiple of 1,...,n by taking the Finset lcm of i+1 over i in range n. Then every positive r≤n divides d_n.
-- source:
--   Standard least-common-multiple property used in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

theorem RhinViola.rangeLcmDivides
    (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    r ∣ (Finset.range n).lcm (fun i : ℕ => i + 1) := by sorry
