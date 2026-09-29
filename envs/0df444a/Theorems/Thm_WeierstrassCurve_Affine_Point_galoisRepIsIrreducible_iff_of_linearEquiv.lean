-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv
-- name    : WeierstrassCurve.Affine.Point.galoisRepIsIrreducible_iff_of_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/04104a35-257a-5017-bd3e-3b91a4c093d2
-- title:
--   Irreducibility of mod-n torsion transfers along equivariant isomorphisms
-- statement:
--   Let $F$ be a field, $K$ a field equipped with an $F$-algebra structure (with decidable equality), let $E_1,E_2$ be Weierstrass curves over $F$ and $n$ a natural number. Write $A_i$ for the $n$-torsion subgroup $\mathrm{torsionBy}_{\mathbb Z}(E_i(K),n)$ of the group of affine $K$-points of the base change of $E_i$ to $K$, regarded as a module over $\mathbb{Z}/n\mathbb{Z}$, on which the group $K\simeq_{\mathrm{alg}[F]}K$ of $F$-algebra automorphisms of $K$ acts. Suppose given a $\mathbb{Z}/n\mathbb{Z}$-linear isomorphism $\varphi\colon A_1\to A_2$ satisfying $\varphi(\sigma\cdot x)=\sigma\cdot\varphi(x)$ for all $F$-algebra automorphisms $\sigma$ of $K$ and all $x\in A_1$. Then `GaloisRepIsIrreducible` holds for $E_1$ if and only if it holds for $E_2$; that is, $A_1$ is nontrivial and its only $\mathbb{Z}/n\mathbb{Z}$-submodules $N$ with $\sigma\cdot x\in N$ for all $\sigma$ and all $x\in N$ are $\bot$ and $\top$, precisely when the same two conditions hold for $A_2$. No primality, separability or normality hypotheses are imposed: the acting group is the full automorphism group $\mathrm{Aut}(K/F)$ and $n$ is arbitrary.
--
--   This is the statement that irreducibility of the mod-$n$ representation on torsion points, in the elementary form "no proper nonzero $\mathrm{Aut}(K/F)$-stable $\mathbb{Z}/n\mathbb{Z}$-submodule", depends only on the torsion module together with its automorphism action, and hence transports along any equivariant linear isomorphism $E_1(K)[n]\cong E_2(K)[n]$. It is used to move the irreducibility hypothesis between different models of a curve, and is cited by [`WeierstrassCurve.galoisRepIsIrreducible_iff_of_variableChange_eq`](thm.html#WeierstrassCurve.galoisRepIsIrreducible_iff_of_variableChange_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv.lean

import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.Affine.Point.galoisRepIsIrreducible_iff_of_linearEquiv {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] [DecidableEq K] {E₁ E₂ : WeierstrassCurve F} {n : ℕ} (φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n) (hφ : ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x) : GaloisRepIsIrreducible (K := K) F E₁ n ↔ GaloisRepIsIrreducible (K := K) F E₂ n := by sorry
