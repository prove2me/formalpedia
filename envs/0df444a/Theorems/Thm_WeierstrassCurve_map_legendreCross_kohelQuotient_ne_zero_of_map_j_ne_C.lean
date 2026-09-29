-- Prove2me | Theorems.Thm_WeierstrassCurve_map_legendreCross_kohelQuotient_ne_zero_of_map_j_ne_C
-- name    : WeierstrassCurve.map_legendreCross_kohelQuotient_ne_zero_of_map_j_ne_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/d61cf430-de0c-5dd3-8a2e-c0dc74efc0ff
-- title:
--   Legendre cross-difference of a non-isotrivial family and its Kohel quotient
-- statement:
--   Let $\mathcal{O}$ be a local integral domain of characteristic $0$, let $k$ be a field, let $\pi\colon\mathcal{O}\to k$ be a surjective ring homomorphism, and suppose $2\neq 0$ in $k$. Let $E$ be a Weierstrass curve over $\mathcal{O}[[T]]$ with $\Delta(E)$ a unit, and assume that the coefficientwise image $\pi_*j(E)\in k[[T]]$ is not a constant power series, i.e. differs from the constant series with the same constant coefficient. Fix $n\in\mathbb{N}$ with $2n+1\neq 0$ in $k$ and $2n+1$ not a square in $\mathbb{N}$. Write $\rho=\pi\circ(\text{constant coefficient})\colon\mathcal{O}[[T]]\to k$, and let $Q_0$ be an affine point of $\rho_*E$ of exact order $2n+1$. Let $h\in\mathcal{O}[[T]][X]$ be monic, dividing the division polynomial $\mathrm{pre}\Psi'_{2n+1}(E)$, with $\rho_*h=\prod(X-x)$ over the set of first coordinates of $\mathrm{coordsOrZero}(kQ_0)$ for $1\le k\le n$ (the value $(0,0)$ being taken at the zero point). Assume Kohel's quotient $E'=E/h$, obtained from $E$ by replacing $a_4$ by $a_4-5t$ and $a_6$ by $a_6-b_2t-7w$ with $t=6p_2+b_2p_1+(\deg h)b_4$ and $w=10p_3+2b_2p_2+3b_4p_1+(\deg h)b_6$ in the root power sums $p_i$ of $h$, has unit discriminant. Let $e_1,e_2\in\mathcal{O}[[T]]$ be roots of $\Psi_2^2(E)=4x^3+b_2x^2+2b_4x+b_6$ with $\pi_*(e_2-e_1)\neq0$, and $e'_1,e'_2$ roots of $\Psi_2^2(E')$ with $\pi_*(e'_2-e'_1)\neq0$. Then $$\pi_*\bigl((-b_2(E)-8e_1-4e_2)(e'_2-e'_1)-(-b_2(E')-8e'_1-4e'_2)(e_2-e_1)\bigr)\neq 0$$ in $k[[T]]$.
--
--   Since $e_1+e_2+e_3=-b_2/4$, the two factors $-b_2-8e_1-4e_2=4(e_3-e_1)$ record the numerators of the Legendre parameters $\lambda=(e_3-e_1)/(e_2-e_1)$ of the marked families, so the conclusion is the cross-multiplied assertion that $\lambda(E)$ and $\lambda(E')$ have distinct reductions in $k[[T]]$; it is the level-$2$ refinement of the statement that a non-isotrivial family is not isomorphic to its quotient by a cyclic subgroup of non-square odd order. It feeds the construction of a power-series deformation along which a curve and its Kohel quotient become isomorphic compatibly with the two-torsion, a step in the deformation-theoretic treatment of Deuring's lifting theorem in residue characteristic different from $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_map_legendreCross_kohelQuotient_ne_zero_of_map_j_ne_C.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_KernelPolynomial
import Definitions.Def_WeierstrassCurve_KohelQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.map_legendreCross_kohelQuotient_ne_zero_of_map_j_ne_C
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [DecidableEq k] (π : 𝒪 →+* k) (hπ : Function.Surjective π)
    (h2 : (2 : k) ≠ 0)
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
    {e₁ e₂ e'₁ e'₂ : PowerSeries 𝒪}
    (he₁ : E.Ψ₂Sq.eval e₁ = 0) (he₂ : E.Ψ₂Sq.eval e₂ = 0)
    (he : PowerSeries.map π (e₂ - e₁) ≠ 0)
    (he'₁ : (E.kohelQuotient h).Ψ₂Sq.eval e'₁ = 0)
    (he'₂ : (E.kohelQuotient h).Ψ₂Sq.eval e'₂ = 0)
    (he' : PowerSeries.map π (e'₂ - e'₁) ≠ 0) :
    PowerSeries.map π ((-E.b₂ - 8 * e₁ - 4 * e₂) * (e'₂ - e'₁)
      - (-(E.kohelQuotient h).b₂ - 8 * e'₁ - 4 * e'₂) * (e₂ - e₁)) ≠ 0 := by sorry
