-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_tate_origin_addOrderOf_eq_four_five_six_seven_iff
-- name    : WeierstrassCurve.Affine.tate_origin_addOrderOf_eq_four_five_six_seven_iff
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T00:56:36.115261+00:00
-- url     : https://prove2.me/theorems/9ebde9cb-4053-46db-a4bd-b106a99142aa
-- title:
--   Kubert's table for orders 4 to 7: on the Tate normal form $E_{b,c}$ the point $(0,0)$ has order $4, 5, 6, 7$ exactly when $c = 0$, $b = c$, $b = c + c^2$, $b^2 - bc - c^3 = 0$
-- statement:
--   Let $F$ be a field and let $b, c \in F$ with $b \neq 0$. Let $E_{b,c}$ be the Weierstrass cubic in Tate normal form
--
--   $$E_{b,c} : y^2 + (1 - c)xy - by = x^3 - bx^2,$$
--
--   on which the point $P = (0, 0)$ is nonsingular (this holds exactly when $b \neq 0$). In the group of nonsingular points of $E_{b,c}$ over $F$:
--
--   1. $P$ has exact order $4$ if and only if $c = 0$;
--   2. $P$ has exact order $5$ if and only if $b = c$;
--   3. $P$ has exact order $6$ if and only if $b = c + c^2$;
--   4. $P$ has exact order $7$ if and only if $b^2 - bc - c^3 = 0$.
--
--   These are the first rows of Kubert's table of universal curves with a point of given order: $E_{t,t}$ for order $5$, $E_{t + t^2, t}$ for order $6$, and $b = d^3 - d^2$, $c = d^2 - d$ (a rational parametrisation of $b^2 = bc + c^3$) for order $7$. No condition on the discriminant is needed; if $\Delta(E_{b,c}) = 0$ the statement is about the group of nonsingular points of the singular cubic. Example: over $\mathbb Q$, $b = c = 1$ gives $y^2 - y = x^3 - x^2$ (the curve 11a3), on which $(0,0)$ has order $5$.
--
--   Proof idea: the chord-tangent law gives $2P = (b, bc)$, $-2P = (b, 0)$, $3P = (c, b - c)$, $-3P = (c, c^2)$. So $4P = 0$ iff $2P = -2P$ iff $c = 0$; $5P = 0$ iff $3P = -2P$ iff $b = c$; $6P = 0$ iff $3P = -3P$ iff $b - c = c^2$; and $7P = 0$ iff $4P = -3P$, which after clearing the denominators of $x(4P)$ is $b^2 - bc - c^3 = 0$. In each case the smaller multiples are nonzero because $b \neq 0$.
--
--   Role: with every point of order $N \ge 4$ moving to $(0,0)$ on a unique $E_{b,c}$, this makes $Y_1(N)$ explicit for the genus-zero levels $N = 4, 5, 6, 7$, for example for counting curves with a point of order $N$ over a finite field.
--
--   **Formalization Note**: the curve is the Mathlib Weierstrass curve `{ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve F` and $P$ is `WeierstrassCurve.Affine.Point.some 0 0 h`, where `h` is the nonsingularity of $(0,0)$, as in the platform's other Tate normal form statements. The exact order is `addOrderOf` in Mathlib's group `W.toAffine.Point` (nonsingular affine points and the point at infinity), whose group law uses `[DecidableEq F]`. There is no `IsElliptic` hypothesis, so the statement also covers singular $E_{b,c}$. The condition $c \neq 0$ that Kubert's table lists for orders $6$ and $7$ is implied by $b \neq 0$ here (if $c = 0$ the right-hand sides force $b = 0$). The four equivalences are the four conjuncts.
-- source:
--   D. S. Kubert, Universal bounds on the torsion of elliptic curves, Proc. London Math. Soc. (3) 33 (1976), 193-237; D. Husemoller, Elliptic Curves, 2nd ed., GTM 111, Springer 2004, Section 4.4

import Mathlib

set_option autoImplicit false

theorem WeierstrassCurve.Affine.tate_origin_addOrderOf_eq_four_five_six_seven_iff
    {F : Type*} [Field F] [DecidableEq F] (b c : F) (hb : b ≠ 0)
    (h : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve F).toAffine.Nonsingular 0 0) :
    (addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = 4 ↔ c = 0) ∧
    (addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = 5 ↔ b = c) ∧
    (addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = 6 ↔ b = c + c ^ 2) ∧
    (addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = 7 ↔ b ^ 2 - b * c - c ^ 3 = 0) := by
  sorry
