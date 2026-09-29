-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective
-- name    : P2M.Dup.AlgebraicCurve.IsFrobeniusEndo.restrictAlong_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/53bf93d4-3a28-5989-94f0-c51059160eca
-- title:
--   Frobenius endomorphisms are radicial on places
-- statement:
--   Let $K$ be a field and $F$ a field equipped with a $K$-algebra structure, and let $\varphi : F \to F$ be a $K$-algebra endomorphism. Fix $\ell \in \mathbb{N}$ and assume $h$: $\varphi$ is a Frobenius endomorphism of exponent $\ell$ in the sense of [`AlgebraicCurve.IsFrobeniusEndo`](def/AlgebraicCurve_FrobeniusEndo.html#L16), i.e. for every $x \in F$ there is $y \in F$ with $\varphi(y) = x^{\ell}$, and for every $y \in F$ there is $x \in F$ with $\varphi(y) = x^{\ell}$. Assume further $\ell \neq 0$ and that the underlying ring homomorphism of $\varphi$ is integral. Then the restriction map on places of $F$ over $K$ along $\varphi$ is injective. Here a place of $F$ over $K$ is a valuation subring of $F$ which contains the image of $K$, is not all of $F$, and is a principal ideal ring; and [`AlgebraicCurve.Place.restrictAlong`](def/AlgebraicCurve_Correspondence.html#L204) sends a place $w$ to the place whose valuation subring is the preimage $\varphi^{-1}(\mathcal{O}_w)$, obtained by regarding $F$ as an $F$-algebra via $\varphi$ and restricting $w$ along that algebra structure. The proof uses only the first clause of the Frobenius hypothesis, that every $\ell$-th power lies in the image of $\varphi$.
--
--   This is the radiciality of a purely inseparable (relative Frobenius) endomorphism at the level of places: a place of $F$ is determined by its pullback along $\varphi$. It is used, together with a count of fixed points, in [`AlgebraicCurve.natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq`](thm.html#AlgebraicCurve.natCard_fixedPoints_restrictAlong_lt_of_isFrobeniusEndo_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_IsFrobeniusEndo_restrictAlong_injective.lean

import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import Definitions.Def_AlgebraicCurve_FrobeniusEndoPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.IsFrobeniusEndo.restrictAlong_injective {K F : Type*} [Field K] [Field F] [Algebra K F] {φ : F →ₐ[K] F} {ℓ : ℕ} (h : AlgebraicCurve.IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0) (hφ : φ.IsIntegral) : Function.Injective (AlgebraicCurve.Place.restrictAlong φ hφ) := by sorry
