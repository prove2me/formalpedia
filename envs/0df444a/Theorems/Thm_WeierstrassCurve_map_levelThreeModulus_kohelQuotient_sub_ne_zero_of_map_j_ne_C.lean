-- Prove2me | Theorems.Thm_WeierstrassCurve_map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C
-- name    : WeierstrassCurve.map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/b1b0c3e4-de97-5e83-a77a-37279ace61dd
-- title:
--   Level-three moduli of E and E/h differ modulo π
-- statement:
--   Let $\mathcal O$ be a local integral domain of characteristic $0$, let $k$ be a field with decidable equality, let $\pi\colon\mathcal O\to k$ be a surjective ring homomorphism, and assume $3\neq 0$ in $k$. Let $E$ be a Weierstrass curve over $\mathcal O[[T]]$ whose discriminant is a unit, and assume that the coefficientwise image `PowerSeries.map π E.j` of its $j$-invariant is not the constant series given by its own constant coefficient. Fix $n\in\mathbb N$ with $2n+1\neq 0$ in $k$ and $2n+1$ not a square, and let $Q_0$ be a point of exact additive order $2n+1$ on the affine curve obtained from $E$ by the homomorphism `PowerSeries.constantCoeff` followed by $\pi$. Let $h\in\mathcal O[[T]][X]$ be monic, dividing `E.preΨ' (2 * n + 1)`, whose image under that same homomorphism equals $\prod_{P\in S}(X-P_1)$ with $S$ the finite set of `coordsOrZero` of $k\cdot Q_0$ for $1\le k\le n$; assume the Kohel quotient `E.kohelQuotient h` — the Weierstrass curve with $a_1,a_2,a_3$ unchanged, $a_4-5t$ and $a_6-b_2t-7w$, where $t$ and $w$ are `E.kohelT h` and `E.kohelW h`, built from the root power sums of $h$, the invariants $b_2,b_4,b_6$ and $\deg h$ — again has unit discriminant. Finally let $x_1,y_1,x_2\in\mathcal O[[T]]$ satisfy the affine equation of $E$ at $(x_1,y_1)$, with $x_1$ and $x_2$ roots of `E.Ψ₃`, with `E.deuringA₃ x₁ y₁` a unit and `PowerSeries.map π (x₂ - x₁) ≠ 0`, and let $x_1',y_1',x_2'$ satisfy the same four conditions for `E.kohelQuotient h`. Then the coefficientwise reduction along $\pi$ of $$(E/h).\mathrm{levelThreeModulus}(x_1',y_1',x_2')-E.\mathrm{levelThreeModulus}(x_1,y_1,x_2)$$ is nonzero in $k[[T]]$, where $\mathrm{levelThreeModulus}(x_1,y_1,x_2)=\mathrm{deuringA}_1(x_1,y_1)\,(x_2-x_1)\,\mathrm{Ring.inverse}(\mathrm{deuringA}_3(x_1,y_1))$.
--
--   This is the level-three form of the statement that a non-isotrivial family of elliptic curves over a formal disc is not isomorphic, as a marked family, to its quotient by a lifted cyclic subgroup of non-square order; in Deuring's deformation-theoretic proof of the lifting theorem in residue characteristic $2$, where three-torsion rather than two-torsion is étale, it is the input to Weierstrass preparation. It is used by [`WeierstrassCurve.exists_powerSeries_deformation_kohelQuotient_threeTorsion_levelThreeModulus_of_smul_eq_veluQuotient`](thm.html#WeierstrassCurve.exists_powerSeries_deformation_kohelQuotient_threeTorsion_levelThreeModulus_of_smul_eq_veluQuotient), which produces a point of the disc at which the marked family and its marked quotient agree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Definitions.Def_WeierstrassCurve_KohelQuotient
import Definitions.Def_WeierstrassCurve_LevelThreeModulus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.map_levelThreeModulus_kohelQuotient_sub_ne_zero_of_map_j_ne_C
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [DecidableEq k] (π : 𝒪 →+* k) (hπ : Function.Surjective π)
    (h3 : (3 : k) ≠ 0)
    (E : WeierstrassCurve (PowerSeries 𝒪)) [E.IsElliptic]
    (hj : PowerSeries.map π E.j ≠
      PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.map π E.j)))
    {n : ℕ} (hm : ((2 * n + 1 : ℕ) : k) ≠ 0) (hsq : ¬ IsSquare (2 * n + 1))
    (Q₀ : (E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).toAffine.Point)
    (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    {h : Polynomial (PowerSeries 𝒪)} (hh : h.Monic) (hdvd : h ∣ E.preΨ' (2 * n + 1))
    (hmap : h.map (π.comp (PowerSeries.constantCoeff (R := 𝒪))) =
      WeierstrassCurve.kernelPolynomial
        ((E.map (π.comp (PowerSeries.constantCoeff (R := 𝒪)))).oddOrderSummingSet Q₀ n))
    [(E.kohelQuotient h).IsElliptic]
    {x₁ y₁ x₂ : PowerSeries 𝒪} (hP₁ : E.toAffine.Equation x₁ y₁)
    (hx₁ : E.Ψ₃.eval x₁ = 0) (hx₂ : E.Ψ₃.eval x₂ = 0)
    (hA₃ : IsUnit (E.deuringA₃ x₁ y₁)) (hx : PowerSeries.map π (x₂ - x₁) ≠ 0)
    {x₁' y₁' x₂' : PowerSeries 𝒪} (hP₁' : (E.kohelQuotient h).toAffine.Equation x₁' y₁')
    (hx₁' : (E.kohelQuotient h).Ψ₃.eval x₁' = 0) (hx₂' : (E.kohelQuotient h).Ψ₃.eval x₂' = 0)
    (hA₃' : IsUnit ((E.kohelQuotient h).deuringA₃ x₁' y₁'))
    (hx' : PowerSeries.map π (x₂' - x₁') ≠ 0) :
    PowerSeries.map π ((E.kohelQuotient h).levelThreeModulus x₁' y₁' x₂'
      - E.levelThreeModulus x₁ y₁ x₂) ≠ 0 := by sorry
