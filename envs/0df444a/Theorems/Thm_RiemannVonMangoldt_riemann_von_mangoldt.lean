-- Prove2me | Theorems.Thm_RiemannVonMangoldt_riemann_von_mangoldt
-- name    : RiemannVonMangoldt.riemann_von_mangoldt
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T02:10:34.80099+00:00
-- url     : https://prove2.me/theorems/a365b15d-8cc3-467c-bb49-2d3705c8b1b2
-- title:
--   Riemann–von Mangoldt formula: $N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+O(\log T)$
-- statement:
--   Write $N(T)$ for the number of zeros $\rho$ of the Riemann zeta function $\zeta(s)$ with $0<\operatorname{Re}\rho<1$ and $0<\operatorname{Im}\rho\le T$, counted with multiplicity. The **Riemann–von Mangoldt formula** states that
--   $$N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+O(\log T)\qquad (T\to\infty),$$
--   that is, there are constants $C$ and $T_0$ such that $\bigl|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi}+\frac{T}{2\pi}\bigr|\le C\log T$ for all $T\ge T_0$.
--
--   The formula was stated by Riemann in 1859 and proved by von Mangoldt in 1905. It is the basic quantitative statement about the vertical distribution of the nontrivial zeros: the zeros up to height $T$ number about $\frac{T}{2\pi}\log T$, and their average spacing at height $T$ is about $2\pi/\log T$.
--
--   **Formalization Note** $N(T)$ is `zetaZeroCount T` from `Definitions.Def_RiemannVonMangoldt_ZeroCounts`; the $O(\log T)$ is Mathlib's `Asymptotics.IsBigO` along `Filter.atTop`.
-- source:
--   Wikipedia, "Riemann–von Mangoldt formula", revision oldid=1362774495 (https://en.wikipedia.org/w/index.php?title=Riemann–von_Mangoldt_formula&oldid=1362774495), first displayed formula (statement of the Riemann–von Mangoldt formula). Riemann 1859; von Mangoldt 1905; Titchmarsh (1986) Theorem 9.4.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts

open Filter Asymptotics Real

namespace RiemannVonMangoldt

theorem riemann_von_mangoldt :
    (fun T : ℝ => zetaZeroCount T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π)))
      =O[atTop] Real.log := by sorry

end RiemannVonMangoldt
