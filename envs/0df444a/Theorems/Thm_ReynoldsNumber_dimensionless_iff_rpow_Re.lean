-- Prove2me | Theorems.Thm_ReynoldsNumber_dimensionless_iff_rpow_Re
-- name    : ReynoldsNumber.dimensionless_iff_rpow_Re
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:29:54.26107+00:00
-- url     : https://prove2.me/theorems/8a073270-3582-4260-a137-4325986f085d
-- title:
--   Goal: every dimensionless monomial in $\rho,u,L,\mu$ is a real power of $Re$
-- statement:
--   Fix positive values of the density $\rho$, the flow velocity $u$, the characteristic length $L$ and the dynamic viscosity $\mu$. For real exponents $a,b,c,d$ the monomial $\rho^{a}u^{b}L^{c}\mu^{d}$ (real powers, in the sense of `Real.rpow`) is dimensionless if and only if there is a real number $s$ with
--   $$(a,b,c,d)=s\,(1,1,1,-1)\qquad\text{and}\qquad \rho^{a}u^{b}L^{c}\mu^{d}=\mathrm{Re}(\rho,u,L,\mu)^{s}.$$
--   That is: the dimensionless monomials in $\rho,u,L,\mu$ are exactly the real powers of the Reynolds number, so any dimensionless quantity built as such a monomial is a function of $\mathrm{Re}$ alone.
-- source:
--   Wikipedia, “Reynolds number” (uploaded PDF, Reynolds_number.pdf), sections “Definition”, “Derivation”, “Alternative derivation”, “Flow in a pipe”: https://en.wikipedia.org/wiki/Reynolds_number

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_ReynoldsNumber_core

namespace ReynoldsNumber

theorem dimensionless_iff_rpow_Re (rho u L mu : ℝ) (hrho : 0 < rho) (hu : 0 < u)
    (hL : 0 < L) (hmu : 0 < mu) (a b c d : ℝ) :
    Dimensionless a b c d ↔
      ∃ s : ℝ, (a, b, c, d) = (s, s, s, -s) ∧
        rho ^ a * u ^ b * L ^ c * mu ^ d = Re rho u L mu ^ s := by sorry

end ReynoldsNumber
