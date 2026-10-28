-- Prove2me | Theorems.Thm_ProblemSpec_Equilibrium_rg_lt_rbar
-- name    : ProblemSpec.Equilibrium.rg_lt_rbar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:30.40576+00:00
-- url     : https://prove2.me/theorems/f90424ad-daac-47ba-ad57-8b2c18e2cfc0
-- title:
--   App. p. 1 — r̄^g < r̄ for every N
-- statement:
--   For every number of participants $N>1$ at which the guessing threshold
--   $$\bar r^g=\frac{1}{\ln(1/p)}\ln\Big(\frac{N-1}{N^2}\frac{\nu w}{\mu}\frac{A}{c_2}\frac{1}{\ln(1/p)}-\frac{c_g}{c_2}\frac1{\ln(1/p)}\Big)$$
--   is defined (its logarithm's argument is positive),
--   $$\bar r^g<\bar r=\frac{1}{\ln(1/p)}\ln\Big(\frac{N-1}{N^2}\frac{w}{\mu}\frac{A}{c_2}\frac{1}{\ln(1/p)}\Big).$$
--
--   The inequality makes the three regions of (A.2) well ordered: Region 0 ($S_r<\bar r^g$), Region I ($\bar r^g\le S_r\le\bar r$), Region II ($S_r>\bar r$).
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), App. p. 1 (PDF 29), sentence after the r̄ formula

import Mathlib
import Definitions.Def_ProblemSpec_Equilibrium_Model

namespace ProblemSpec.Equilibrium

/-- App. p. 1 (PDF 29): "Since `cg > 0` and `ν ∈ (0,1)`, we have `r̄^g < r̄`, for any `N`."
Stated for every `N > 1` at which the formula for `r̄^g` is defined (its logarithm's argument
is positive). -/
theorem rg_lt_rbar (P : Params) (hP : P.Standing) (N : ℝ) (hN : 1 < N) (hg : 0 < rgArg P N) :
    rg P N < rbar P N := by sorry

end ProblemSpec.Equilibrium
