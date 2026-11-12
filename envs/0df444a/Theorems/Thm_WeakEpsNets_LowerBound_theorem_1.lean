-- Prove2me | Theorems.Thm_WeakEpsNets_LowerBound_theorem_1
-- name    : WeakEpsNets.LowerBound.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:01.517609+00:00
-- url     : https://prove2.me/theorems/a66778a0-c601-4a59-b0e5-79538d269ddc
-- title:
--   Theorem 1 — dimension-dependent lower bounds for weak epsilon-nets
-- statement:
--   For every integer $d\ge3$, define
--   $$\gamma_d=\frac12\left\lfloor\frac{\sqrt{8d+25}-1}{2}\right\rfloor.$$
--   There exist positive constants $r_d,c_d$ such that, for every real $r\ge r_d$, both of the following hold:
--   1. There is a finite nonempty $P\subset\mathbb R^d$ such that every finite weak $1/r$-net $X$ for all convex ranges has $|X|\ge c_dr^{\gamma_d}$.
--   2. The worst-case minimum net cardinality satisfies
--   $$f_d(r)\ge c_dr^{\gamma_d}.$$
--   The same constants serve both assertions. Thus $f_d(r)=\Omega_d(r^{\gamma_d})$. This is the full headline theorem: the dimension is arbitrary, the threshold parameter is real, and net points may be anywhere in the ambient space.
--
--   Differences from the source:
--   - reading: constants $r_d>0$ and $c_d$, followed by the $\Omega_d$ conclusion → both $r_d$ and $c_d$ are positive; reason: the asymptotic lower bound requires a positive multiplicative constant; this removes the vacuous zero-constant reading
--   - encoding: finite point sets in $\mathbb R^d$, integer $d\ge3$, and real powers → finite sets of real functions on $\mathrm{Fin}\,d$, natural $d\ge3$, and Real.rpow; reason: nonnegative integer dimensions and finite coordinate functions describe precisely the source instances, including half-integer exponents
--   - encoding: $f_d(r)$ is the supremum of the minimum finite net cardinalities and is $\Omega_d(r^{\gamma_d})$ → the supremum is in $\mathbb N\cup\{+\infty\}$ and the same eventual lower bound is compared in $\mathbb R_{\ge0}\cup\{+\infty\}$; reason: extended orders preserve unbounded values and the explicit positive constants express the source asymptotic assertion without changing an instance
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), Theorem 1, p. 3, lines 81–84; weak-net and extremal definitions pp. 1–2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Extremal
import Definitions.Def_WeakEpsNets_LowerBound_Parameters

open scoped ENNReal

namespace WeakEpsNets.LowerBound

/-- Theorem 1, source p. 3, both the point-set assertion and its f_d consequence.
The positive constant c_d is the reading forced by the printed Ω_d conclusion. -/
theorem theorem_1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ r_d : ℝ, 0 < r_d ∧ ∃ c_d : ℝ, 0 < c_d ∧
      ∀ r : ℝ, r_d ≤ r →
        (∃ P : Finset (Fin d → ℝ), P.Nonempty ∧
          ∀ X : Finset (Fin d → ℝ), IsWeakNet P r X →
            c_d * Real.rpow r (gamma d) ≤ (X.card : ℝ)) ∧
        ENNReal.ofReal (c_d * Real.rpow r (gamma d)) ≤ (f d r : ℝ≥0∞) := by sorry

end WeakEpsNets.LowerBound
