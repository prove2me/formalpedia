-- Prove2me | Theorems.Thm_Pade_pade_normalization
-- name    : Pade.pade_normalization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:53:21.638962+00:00
-- url     : https://prove2.me/theorems/d3d2dd2d-713a-45de-9ec2-a775deebbb9d
-- title:
--   Normalizing the denominator to $1 + b_1x + \cdots + b_nx^n$
-- statement:
--   **Normalization of the denominator.** Let $F$ be a field, $f \in F[[x]]$, $m, n \ge 0$, and let $(P,Q)$ be a Padé pair of type $[m/n]$ for $f$ whose denominator does not vanish at the origin, $q_0 := Q(0) \ne 0$. Then the rescaled pair $(q_0^{-1}P,\; q_0^{-1}Q)$ is again a Padé pair of type $[m/n]$ for $f$, and
--
--   $$ \big(q_0^{-1}Q\big)(0) \;=\; 1 . $$
--
--   In other words, whenever the $[m/n]$ entry is not defective one may always arrange the denominator in the normalized shape used in the source's definition,
--
--   $$ R(x) \;=\; \frac{a_0 + a_1x + \cdots + a_mx^m}{1 + b_1x + b_2x^2 + \cdots + b_nx^n}, $$
--
--   without changing the rational function or the order of contact with $f$. This records that the normalization $b_0 = 1$ is a convention and not an extra constraint: the solution set of the linearized problem is stable under multiplication by a nonzero scalar, and the scalar $q_0^{-1}$ is the one that produces the displayed form.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Definition' (the displayed normalized form of $R(x)$)

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

namespace Pade

theorem pade_normalization {F : Type*} [Field F] (f : PowerSeries F) (m n : ℕ)
    (P Q : Polynomial F) (h : IsPadeApproximant f m n P Q) (hQ : Q.coeff 0 ≠ 0) :
    IsPadeApproximant f m n (C (Q.coeff 0)⁻¹ * P) (C (Q.coeff 0)⁻¹ * Q) ∧
      (C (Q.coeff 0)⁻¹ * Q).coeff 0 = 1 := by sorry

end Pade
