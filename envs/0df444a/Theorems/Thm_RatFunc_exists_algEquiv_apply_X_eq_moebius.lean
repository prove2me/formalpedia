-- Prove2me | Theorems.Thm_RatFunc_exists_algEquiv_apply_X_eq_moebius
-- name    : RatFunc.exists_algEquiv_apply_X_eq_moebius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/abff6a91-6445-5f18-8bc7-7719f4df1096
-- title:
--   Möbius substitutions are K-automorphisms of K(X)
-- statement:
--   Let $K$ be a field and let $a,b,c,d \in K$ satisfy $ad-bc \neq 0$. The assertion is that there exists a $K$-algebra automorphism $\varphi$ of the rational function field `RatFunc K` (an element of `RatFunc K ≃ₐ[K] RatFunc K`) whose value on the canonical transcendental generator `RatFunc.X` is the linear fractional expression $(aX+b)/(cX+d)$, formed from the images of $a,b,c,d$ under the constant-embedding `RatFunc.C` and the field operations of `RatFunc K`. Only the value of $\varphi$ at `RatFunc.X` is prescribed; since `RatFunc K` is generated over $K$ by `RatFunc.X`, this determines $\varphi$ as the substitution $f(X) \mapsto f\bigl((aX+b)/(cX+d)\bigr)$, but the statement records existence of the automorphism only, with no uniqueness claim and no group-theoretic statement about the resulting action of $\mathrm{PGL}_2(K)$.
--
--   This is the classical fact that linear fractional substitutions with invertible coefficient matrix induce $K$-automorphisms of the rational function field. It is used in the project to move points and places of the rational function field around — for instance to normalise a chosen place against the place at infinity — and in the verification that certain division-polynomial-type expressions attached to the Klein curve and to Rubin–Silverberg members do not vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RatFunc_exists_algEquiv_apply_X_eq_moebius.lean

import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem RatFunc.exists_algEquiv_apply_X_eq_moebius {K : Type*} [Field K] (a b c d : K) (hdet : a * d - b * c ≠ 0) : ∃ φ : RatFunc K ≃ₐ[K] RatFunc K, φ RatFunc.X = (RatFunc.C a * RatFunc.X + RatFunc.C b) / (RatFunc.C c * RatFunc.X + RatFunc.C d) := by sorry
