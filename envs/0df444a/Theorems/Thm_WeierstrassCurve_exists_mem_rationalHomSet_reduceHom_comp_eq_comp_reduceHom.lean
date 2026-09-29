-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom
-- name    : WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/cd49331c-a1b0-51ef-9120-12c277d4bf79
-- title:
--   Reduction of geometric homomorphisms at good reduction
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with residue field $\kappa =$ `IsLocalRing.ResidueField A` and residue map $\mathrm{red} =$ `IsLocalRing.residue A`, and let $E_1, E_2$ be Weierstrass curves with coefficients in $A$ whose reductions $E_i$ mod the maximal ideal of $A$ have nonzero discriminant, $(E_i.\mathrm{map}\,\mathrm{red})\Delta \neq 0$. Let $\mu$ be an additive homomorphism from the group of affine points of $E_1$ over $L$ (i.e. of $E_1$ pushed forward along $A \hookrightarrow L$) to that of $E_2$ over $L$, and assume $\mu$ lies in [`WeierstrassCurve.rationalHomSet L`](def/WeierstrassCurve_RationalEnd.html#L28), that is: either $\mu = 0$, or there are four polynomials $n_X, d_X, n_Y, d_Y \in L[X][Y]$ and a finite set $B \subseteq L$ such that for every nonsingular affine point $(x,y)$ of $E_1$ over $L$ with $x \notin B$ the values of $d_X$ and $d_Y$ at $(x,y)$ are nonzero and $\mu(x,y) = \bigl(n_X(x,y)/d_X(x,y),\, n_Y(x,y)/d_Y(x,y)\bigr)$. Then there exists an additive homomorphism $\nu$ between the point groups of the two reduced curves over $\kappa$, again lying in [`WeierstrassCurve.rationalHomSet`](def/WeierstrassCurve_RationalEnd.html#L28) (so $\nu = 0$ or $\nu$ is given off finitely many abscissae by one such quadruple of polynomials over $\kappa$), such that $\mu$ followed by the reduction map [`WeierstrassCurve.reduceHom hΔ₂`](def/WeierstrassCurve_ReduceHom.html#L481) equals the reduction map [`WeierstrassCurve.reduceHom hΔ₁`](def/WeierstrassCurve_ReduceHom.html#L481) followed by $\nu$ — here `reduceHom` sends the point at infinity to the point at infinity, an affine point $(x,y)$ with $x \in A$ to the residue of $(x,y)$, and an affine point with $x \notin A$ to the point at infinity — and moreover $\nu \neq 0$ whenever $\mu \neq 0$.
--
--   This is the classical statement that an isogeny between elliptic curves with good reduction at a place reduces to an isogeny of the special fibres, compatibly with reduction of points and without becoming zero; in the present rational-map formulation the compatibility also encodes that $\mu$ carries the kernel of reduction into the kernel of reduction. It is used in the construction of nonzero homomorphisms between reduced curves and in the transfer of homomorphism relations (such as $\varphi^2 = [\pm 2]\varphi$-type identities and variable changes) from an algebraically closed field to the residue field of a valuation subring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq L] {A : ValuationSubring L} [DecidableEq (IsLocalRing.ResidueField A)] (E₁ E₂ : WeierstrassCurve A) (hΔ₁ : (E₁.map (IsLocalRing.residue A)).Δ ≠ 0) (hΔ₂ : (E₂.map (IsLocalRing.residue A)).Δ ≠ 0) {μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point} (hμ : μ ∈ WeierstrassCurve.rationalHomSet L (E₁.map A.subtype) (E₂.map A.subtype)) : ∃ ν ∈ WeierstrassCurve.rationalHomSet (IsLocalRing.ResidueField A) (E₁.map (IsLocalRing.residue A)) (E₂.map (IsLocalRing.residue A)), (WeierstrassCurve.reduceHom hΔ₂).comp μ = AddMonoidHom.comp ν (WeierstrassCurve.reduceHom hΔ₁) ∧ (μ ≠ 0 → ν ≠ 0) := by sorry
