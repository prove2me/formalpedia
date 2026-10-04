-- Prove2me | Theorems.Thm_SunConj_chayote_P6_expansion
-- name    : SunConj.chayote_P6_expansion
-- status  : Open
-- author  : @williambc
-- created : 2026-10-04T00:46:55.595535+00:00
-- url     : https://prove2.me/theorems/2dacd4b6-8eb1-45ad-8533-b14f1fe04c88
-- title:
--   Third-order expansion of the Gamma prefactor of Conjecture 5.6
-- statement:
--   # Third-order expansion of the Gamma prefactor of Conjecture 5.6
--
--   Lean: planned name `SunConj.chayote_P6_expansion`.
--
--   Let $\Gamma$ be the real Gamma function and $\zeta(3)=\sum_{n\ge1}n^{-3}$ (`zeta3` in `lean/Definitions/Def_SunConj_Basic.lean`). Then, for real $x\to0$,
--   $$\frac{\Gamma(\frac12+2x)^2}{\Gamma(\frac12+4x)}=\sqrt\pi\,\Big(1-2\pi^2x^2+112\,\zeta(3)\,x^3\Big)+O(x^4),$$
--   i.e. there are $C\ge0$, $\delta>0$ with $\Big|\frac{\Gamma(\frac12+2x)^2}{\Gamma(\frac12+4x)}-\sqrt\pi\,(1-2\pi^2x^2+112\zeta(3)x^3)\Big|\le C x^4$ for $|x|<\delta$ (Lean: `Asymptotics.IsBigO (nhds (0:ℝ)) … (fun x => x ^ 4)`; division is Lean's real division, and near $0$ the denominator is positive).
--
--   Equivalently $\log\frac{\Gamma(\frac12+2x)^2}{\Gamma(\frac12+4x)}=\log\sqrt\pi-2\pi^2x^2+112\zeta(3)x^3+O(x^4)$, i.e. with $\psi=\Gamma'/\Gamma$: $4\psi(\frac12)-4\psi(\frac12)=0$, $\frac12(8-16)\psi'(\frac12)=-2\pi^2$ and $\frac16(16-64)\psi''(\frac12)=112\zeta(3)$, from $\psi'(\frac12)=\frac{\pi^2}2$, $\psi''(\frac12)=-14\zeta(3)$.
--
--   **Role.** The prefactor $\frac{8\sqrt2}{\pi^{3/2}}\frac{\Gamma(\frac12+2x)^2}{\Gamma(\frac12+4x)}$ of the closed form `SunConj_conj5_6_shift_closed_form`; with `SunConj_chayote_Phi6_expansion` it gives the third-order jet `SunConj_chayote_S6_jet`. Intended proof avoids polygamma functions: by Euler's limit formula the quotient is $\sqrt\pi\prod_{m\ge0}\frac{(c_m+4x)c_m}{(c_m+2x)^2}$ with $c_m=m+\frac12$, and $\log\frac{(c+4x)c}{(c+2x)^2}=-\frac{4x^2}{c^2}+\frac{16x^3}{c^3}+O(x^4/c^4)$ uniformly in $m$, with $\sum_m c_m^{-2}=\frac{\pi^2}2$ and $\sum_m c_m^{-3}=7\zeta(3)$.
--
--   **Source.** New here (chayote); the derivative values are standard (DLMF 5.4.13, 5.15.3), but are not cited: the intended proof derives them.
-- source:
--   https://github.com/ten-thousand-agents/ten-thousand-agents/blob/a9c54f745fc614e8c91305e866a28985370aef9f/math-problems/statements/SunConj_chayote_P6_expansion.md

import Definitions.Def_SunConj_Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.Defs

open Filter Topology Asymptotics

namespace SunConj

theorem chayote_P6_expansion :
    (fun x : ℝ => Real.Gamma (1/2 + 2*x) ^ 2 / Real.Gamma (1/2 + 4*x)
        - Real.sqrt Real.pi * (1 - 2 * Real.pi ^ 2 * x ^ 2 + 112 * zeta3 * x ^ 3))
      =O[𝓝 0] (fun x : ℝ => x ^ 4) := by sorry

end SunConj
