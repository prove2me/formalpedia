-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv
-- name    : WeierstrassCurve.Affine.Point.exists_linearEquiv_torsionBy_of_addEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/300c8c6e-2a38-54c7-991f-6db8524dd7d3
-- title:
--   Galois-equivariant group isomorphism restricts to n-torsion
-- statement:
--   Let $F$ be a field, $K$ a field equipped with an $F$-algebra structure, and let $E_1, E_2$ be Weierstrass curves over $F$; write $(E_i⁄K)$ for the base change of $E_i$ to $K$ and $(E_i⁄K).\mathrm{Point}$ for its group of affine points (the affine points together with the point at infinity). Suppose given an isomorphism of additive groups $e \colon (E_1⁄K).\mathrm{Point} \xrightarrow{\sim} (E_2⁄K).\mathrm{Point}$ which is equivariant for the natural action of the group $K \simeq_{\mathrm{alg}[F]} K$ of $F$-algebra automorphisms of $K$, i.e. $e(\sigma \cdot P) = \sigma \cdot e(P)$ for all such $\sigma$ and all $P$. Then for every natural number $n$ there exists a $\mathbb{Z}/n$-linear isomorphism $\varphi$ between the $n$-torsion submodules $\mathrm{torsionBy}_{\mathbb{Z}}\,((E_1⁄K).\mathrm{Point})\,n$ and $\mathrm{torsionBy}_{\mathbb{Z}}\,((E_2⁄K).\mathrm{Point})\,n$, taken for the $\mathbb{Z}/n$-module structures on these groups, such that (i) on underlying points $\varphi$ agrees with $e$, that is $(\varphi x : (E_2⁄K).\mathrm{Point}) = e(x)$ for every $n$-torsion point $x$, and (ii) $\varphi$ is equivariant: $\varphi(\sigma \cdot x) = \sigma \cdot \varphi(x)$ for every $F$-algebra automorphism $\sigma$ of $K$ and every $n$-torsion $x$.
--
--   This is the bookkeeping step passing from an equivariant isomorphism of groups of $K$-points to an isomorphism of the associated mod-$n$ torsion modules as modules with Galois action, i.e. of the mod-$n$ representations attached to the two curves. It is used by [`WeierstrassCurve.exists_linearEquiv_torsionBy_of_variableChange_eq`](thm.html#WeierstrassCurve.exists_linearEquiv_torsionBy_of_variableChange_eq), where the two curves are related by a variable change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.lean

import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.Affine.Point.exists_linearEquiv_torsionBy_of_addEquiv {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] [DecidableEq K] {E₁ E₂ : WeierstrassCurve F} (e : (E₁⁄K).Point ≃+ (E₂⁄K).Point) (he : ∀ (σ : K ≃ₐ[F] K) (P : (E₁⁄K).Point), e (σ • P) = σ • e P) (n : ℕ) : ∃ φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n, (∀ x : Submodule.torsionBy ℤ (E₁⁄K).Point n, (φ x : (E₂⁄K).Point) = e x) ∧ ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x := by sorry
