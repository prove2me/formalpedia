-- Prove2me | Theorems.Thm_Pade_pade_bezout_form
-- name    : Pade.pade_bezout_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:38:43.554654+00:00
-- url     : https://prove2.me/theorems/f1d7bfd9-a2da-4daa-99ff-b2833490fa0f
-- title:
--   Bézout form $P = Q\,T_{m+n} + K\,x^{m+n+1}$
-- statement:
--   **Bézout form of the Padé condition (extended Euclidean algorithm).** Let $F$ be a field, $f \in F[[x]]$, $m, n \ge 0$, and let
--   $$ T_{m+n}(x) \;=\; c_0 + c_1x + \cdots + c_{m+n}x^{m+n} $$
--   be the truncation of $f$ at order $m+n$, where $c_i$ is the coefficient of $x^i$ in $f$. For arbitrary polynomials $P, Q \in F[x]$,
--
--   $$ Q f - P \equiv 0 \pmod{x^{m+n+1}} \quad \Longleftrightarrow \quad \exists\, K \in F[x] : \ P(x) = Q(x)\,T_{m+n}(x) + K(x)\,x^{m+n+1} . $$
--
--   This is the identity the source records as the starting point of the extended-Euclid computation of a Padé approximant: the relation $R = P/Q = T_{m+n} \bmod x^{m+n+1}$ "is equivalent to the existence of some factor $K(x)$ such that $P = Q T_{m+n} + K x^{m+n+1}$", which is read as one Bézout identity in the extended greatest-common-divisor computation for $x^{m+n+1}$ and $T_{m+n}(x)$.
--
--   No hypotheses are imposed on $P$ or $Q$ here — in particular no degree bounds and no condition at the origin — so the lemma isolates exactly the congruence clause of the Padé predicate and converts it from a condition on power series into a polynomial identity, which is the form an algorithmic treatment needs.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Computation' (displays 'R(x) = P(x)/Q(x) = T_{m+n}(x) mod x^{m+n+1}' and 'P(x) = Q(x)T_{m+n}(x) + K(x)x^{m+n+1}')

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

namespace Pade

theorem pade_bezout_form {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ)
    (P Q : Polynomial F) :
    (∀ k ≤ m + n, PowerSeries.coeff k ((Q : PowerSeries F) * f - (P : PowerSeries F)) = 0) ↔
      ∃ K : Polynomial F,
        P = Q * PowerSeries.trunc (m + n + 1) f + K * X ^ (m + n + 1) := by sorry

end Pade
