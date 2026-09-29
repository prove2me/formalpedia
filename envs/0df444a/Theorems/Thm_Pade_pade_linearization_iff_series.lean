-- Prove2me | Theorems.Thm_Pade_pade_linearization_iff_series
-- name    : Pade.pade_linearization_iff_series
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:32:12.253796+00:00
-- url     : https://prove2.me/theorems/9c1588d8-1869-4f27-b5bf-ecee8e4d5c55
-- title:
--   Linearized condition $\iff$ agreement of Maclaurin expansions
-- statement:
--   **The linearized condition equals agreement of Maclaurin expansions.** Let $F$ be a field, $f \in F[[x]]$, $m, n \ge 0$, and let $P, Q \in F[x]$ with $Q(0) \ne 0$, so that $Q$ is invertible in $F[[x]]$. Then
--
--   $$ Q f - P \equiv 0 \pmod{x^{m+n+1}} \quad \Longleftrightarrow \quad f - \frac{P}{Q} \equiv 0 \pmod{x^{m+n+1}} , $$
--
--   both congruences being read coefficientwise: all coefficients of index $k \le m+n$ vanish.
--
--   The right-hand side is the source's formulation, "$f(x) - R(x) = c_{m+n+1}x^{m+n+1} + c_{m+n+2}x^{m+n+2} + \cdots$", i.e. the first $m+n+1$ terms of the Maclaurin expansion of $R = P/Q$ coincide with those of $f$; equivalently, $f$ and $R$ have the same value and the same derivatives at $0$ up to order $m+n$. The left-hand side is the linearized condition used throughout the mission.
--
--   The hypothesis $Q(0) \ne 0$ is what makes the two equivalent, since multiplication by a unit of $F[[x]]$ preserves the order of vanishing; without it the quotient $P/Q$ is not a power series at all. This lemma is the bridge between the mission's algebraic predicate and the analytic statement in the source.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Definition' (display 'f(x) - R(x) = c_{m+n+1}x^{m+n+1} + ⋯')

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

namespace Pade

theorem pade_linearization_iff_series {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ)
    (P Q : Polynomial F) (hQ : Q.coeff 0 ≠ 0) :
    (∀ k ≤ m + n, PowerSeries.coeff k ((Q : PowerSeries F) * f - (P : PowerSeries F)) = 0) ↔
      (∀ k ≤ m + n,
        PowerSeries.coeff k (f - (P : PowerSeries F) * ((Q : PowerSeries F))⁻¹) = 0) := by sorry

end Pade
