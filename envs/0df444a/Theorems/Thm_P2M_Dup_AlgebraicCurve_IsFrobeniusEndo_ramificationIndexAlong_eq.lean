-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq
-- name    : P2M.Dup.AlgebraicCurve.IsFrobeniusEndo.ramificationIndexAlong_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/621b1f6f-a722-5751-91d8-026873eb4367
-- title:
--   Relative Frobenius is totally ramified at every place
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $\varphi : F \to F$ be a $K$-algebra endomorphism, and let $\ell$ be a natural number. Assume [`AlgebraicCurve.IsFrobeniusEndo ℓ φ`](def/AlgebraicCurve_FrobeniusEndo.html#L16), i.e. that for every $x \in F$ there is $y \in F$ with $\varphi(y) = x^{\ell}$, and for every $y \in F$ there is $x \in F$ with $\varphi(y) = x^{\ell}$ (so that the image of $\varphi$ is exactly $F^{\ell}$), and assume $\ell \neq 0$. Let $w$ be a place of $F$ over $K$, that is, a valuation subring of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Then the ramification index of $w$ along $\varphi$ equals $\ell$. Here $F$ is regarded as an algebra over itself via $\varphi$, and the ramification index in question is by definition the infimum of the set of natural numbers $n$ such that $n > 0$ and $\mathrm{ord}_w(\varphi(f)) = n$ for some nonzero $f \in F$; the assertion is that this least positive value of $\mathrm{ord}_w \circ \varphi$ on $F^{\times}$ is $\ell$.
--
--   This is the total ramification of the relative Frobenius: since $\varphi(F) = F^{\ell}$, the extension $F/\varphi(F)$ is purely inseparable of degree dividing a power of the exponent and every place of $F$ is totally ramified over its restriction. It feeds the fundamental identity along $\varphi$ and is used in the comparison of fixed points of a Frobenius square and in the Frobenius pullback computation on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_IsFrobeniusEndo_ramificationIndexAlong_eq.lean

import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.IsFrobeniusEndo.ramificationIndexAlong_eq {K F : Type*} [Field K] [Field F] [Algebra K F] {φ : F →ₐ[K] F} {ℓ : ℕ} (h : AlgebraicCurve.IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0) (w : AlgebraicCurve.Place K F) : AlgebraicCurve.Place.ramificationIndexAlong φ w = ℓ := by sorry
