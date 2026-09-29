-- Prove2me | Theorems.Thm_Pade_pade_unique
-- name    : Pade.pade_unique
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:28:36.208074+00:00
-- url     : https://prove2.me/theorems/29eb0b23-c6d3-4d3b-bff9-d4aa7c242c15
-- title:
--   Uniqueness: any two Padé pairs cross-multiply
-- statement:
--   **Uniqueness of the Padé approximant as a rational function.** Let $F$ be a field, $f \in F[[x]]$, and $m, n \ge 0$. Suppose $(P_1, Q_1)$ and $(P_2, Q_2)$ are both Padé pairs of type $[m/n]$ for $f$, that is, for $i = 1, 2$:
--
--   $$ Q_i \ne 0, \qquad \deg P_i \le m, \qquad \deg Q_i \le n, \qquad Q_i f - P_i \equiv 0 \pmod{x^{m+n+1}} . $$
--
--   Then
--
--   $$ P_1 Q_2 \;=\; P_2 Q_1 \qquad \text{in } F[x]. $$
--
--   This is the exact content of the source's assertion that the Padé approximant, when it exists, is unique. The conclusion is a cross-multiplied identity, not $P_1 = P_2$ and $Q_1 = Q_2$: any pair may be rescaled by a nonzero constant, or multiplied through by a common factor, without leaving the solution set. What is unique is the rational function $P/Q$, hence the formal power series it represents whenever the denominator is invertible.
--
--   The statement holds with no assumption on the constant coefficients of $Q_1, Q_2$, so it also covers defective entries of the Padé table where a denominator vanishes at the origin.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Definition' ('When it exists, the Padé approximant is unique as a formal power series for the given m and n.')

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

namespace Pade

theorem pade_unique {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ)
    (P₁ Q₁ P₂ Q₂ : Polynomial F) (h₁ : IsPadeApproximant f m n P₁ Q₁)
    (h₂ : IsPadeApproximant f m n P₂ Q₂) : P₁ * Q₂ = P₂ * Q₁ := by sorry

end Pade
