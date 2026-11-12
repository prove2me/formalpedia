-- Prove2me | Theorems.Thm_WeakEpsNets_LowerBound_counting_bound
-- name    : WeakEpsNets.LowerBound.counting_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:39.92412+00:00
-- url     : https://prove2.me/theorems/1185a405-370f-495f-9798-e86267fdaa68
-- title:
--   §3 display (line 298) — explicit weak-net cardinality bound
-- statement:
--   Fix integers $s\ge1$ and even $q\ge2$. For the specified lifted grid $P^{+\tau}\subset\mathbb R^{D_s}$, put $r=2(s+1)q^2$. Every finite weak $1/r$-net $X$ with respect to all convex ranges satisfies
--   $$|X|\ge \frac{q^{s+2}}8+\frac{q^2}4.$$
--   The statement retains both summands and the exact coefficients in the paper's counting display. The convex-position and strong half-net facts mentioned immediately before the display remain proof obligations of this milestone; neither is assumed as a hypothesis.
--
--   Differences from the source:
--   - encoding: $\mathbb R^{D_s}$ with the paper's coordinates and hyperplanes indexed by positive integers → real functions on $\mathrm{Fin}(s-1)\sqcup\{(i,j)\in\mathrm{Fin}(s+1)^2:i\le j\}$ and hyperplane parameters in $(\mathrm{Fin}\,q)^s\times\mathrm{Fin}(q^2)$, interpreted as index plus one; reason: the coordinate set has exactly $D_s$ elements for $s\ge1$, and adding one bijects the parameter indices with the source's positive intervals
--   - encoding: the parameter is set to $r=2(s+1)q^2$ before the inequality → the weak-net hypothesis substitutes that real expression for $r$, and the lower bound uses real division by 8 and 4; reason: substitution removes only a redundant parameter and preserves the exact numerical inequality
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), §3, display at line 298, p. 10, with preamble lines 295–297; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Nets
import Definitions.Def_WeakEpsNets_LowerBound_Construction

namespace WeakEpsNets.LowerBound

/-- §3 display at line 298, source p. 10: the explicit lower bound, not just its order. -/
theorem counting_bound (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (heven : Even q)
    (X : Finset (LiftSpace s))
    (hnet : IsWeakNet (liftedGrid s q) (2 * (s + 1 : ℝ) * (q : ℝ) ^ 2) X) :
    (q : ℝ) ^ (s + 2) / 8 + (q : ℝ) ^ 2 / 4 ≤ (X.card : ℝ) := by sorry

end WeakEpsNets.LowerBound
