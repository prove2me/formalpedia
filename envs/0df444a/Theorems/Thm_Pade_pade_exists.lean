-- Prove2me | Theorems.Thm_Pade_pade_exists
-- name    : Pade.pade_exists
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:28:06.957715+00:00
-- url     : https://prove2.me/theorems/a1ac5071-9c5f-4732-b3ff-0f555a0c1d8f
-- title:
--   Existence of a Padé pair of type $[m/n]$
-- statement:
--   **Existence of the $[m/n]$ Padé pair.** Let $F$ be a field, $f \in F[[x]]$ a formal power series and $m, n \ge 0$ integers. Then there exist polynomials $P, Q \in F[x]$ with
--
--   $$ Q \ne 0, \qquad \deg P \le m, \qquad \deg Q \le n, \qquad Q(x)f(x) - P(x) \equiv 0 \pmod{x^{m+n+1}} . $$
--
--   No hypothesis is placed on $f$: the statement covers $f = 0$ and the degenerate indices $m = 0$ or $n = 0$.
--
--   This is the half of the fundamental theorem that makes the Padé table nonempty at every position. The linearization is essential to it: the $n+1$ unknown coefficients of $Q$ are subject to only $n$ homogeneous linear equations (the vanishing of the coefficients of $x^{m+1}, \dots, x^{m+n}$ in $Qf$), so a nonzero $Q$ always exists, and $P$ is then forced as the truncation of $Qf$ at order $m$. The resulting denominator may satisfy $Q(0) = 0$, in which case the associated rational function is not of the normalized shape $1 + b_1x + \cdots$; existence in that normalized sense can genuinely fail, which is why this statement is posed for the linearized problem.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Definition'

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

namespace Pade

theorem pade_exists {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ) :
    ∃ P Q : Polynomial F, IsPadeApproximant f m n P Q := by sorry

end Pade
