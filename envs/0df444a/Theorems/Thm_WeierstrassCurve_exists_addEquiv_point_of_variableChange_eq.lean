-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq
-- name    : WeierstrassCurve.exists_addEquiv_point_of_variableChange_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/8567cd04-3bb6-55c2-bf7b-3b75b310d878
-- title:
--   Variable change over F gives Galois-equivariant isomorphism of K-points
-- statement:
--   Let $F$ be a field, let $K$ be a field equipped with an $F$-algebra structure, and let $E, E'$ be Weierstrass curves over $F$. Let $C$ be a variable change over $F$, that is a tuple $(u, r, s, t)$ with $u \in F^\times$ and $r, s, t \in F$ acting on Weierstrass equations in the usual way, and assume that the result $C \bullet E$ of acting by $C$ on $E$ equals $E'$. The assertion is that there exists an isomorphism of additive groups $e$ from the group of affine points (including the point at infinity) of the curve $E$ base changed to $K$ to the corresponding group for $E'$, such that $e(\sigma \bullet P) = \sigma \bullet e(P)$ for every $F$-algebra automorphism $\sigma$ of $K$ and every $K$-point $P$ of $E$, where $\bullet$ denotes the action of $K \simeq_{\mathrm{alg}[F]} K$ on groups of $K$-points fixed by the project's Galois-representation definitions. The existence statement gives no formula for $e$.
--
--   This is the standard fact that $F$-isomorphic Weierstrass models have isomorphic groups of $K$-points, compatibly with the action of $\mathrm{Aut}(K/F)$, since the coordinate change has coefficients in the base field. It is the transport mechanism used to move Galois-module data between models of a curve, and is cited by [`WeierstrassCurve.exists_addEquiv_point_baseChange_variableChange_smul_algEquiv`](thm.html#WeierstrassCurve.exists_addEquiv_point_baseChange_variableChange_smul_algEquiv) and by [`WeierstrassCurve.exists_linearEquiv_torsionBy_of_variableChange_eq`](thm.html#WeierstrassCurve.exists_linearEquiv_torsionBy_of_variableChange_eq), the latter transferring the $n$-torsion as a Galois module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq.lean

import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_addEquiv_point_of_variableChange_eq {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K] {E E' : WeierstrassCurve F} (C : VariableChange F) (hC : C • E = E') : ∃ e : (E⁄K).Point ≃+ (E'⁄K).Point, ∀ (σ : K ≃ₐ[F] K) (P : (E⁄K).Point), e (σ • P) = σ • e P := by sorry
