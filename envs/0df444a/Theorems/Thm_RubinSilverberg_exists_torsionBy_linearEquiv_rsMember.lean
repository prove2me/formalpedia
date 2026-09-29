-- Prove2me | Theorems.Thm_RubinSilverberg_exists_torsionBy_linearEquiv_rsMember
-- name    : RubinSilverberg.exists_torsionBy_linearEquiv_rsMember
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/882d6c6a-baf9-56a6-a271-09ad0dbe6780
-- title:
--   Constancy of the mod 5 representation in the Rubin–Silverberg family
-- statement:
--   Fix rationals $a,b,l,t_0$ with $a\neq 0$ and $b\neq 0$, and an element $u_0$ of $\overline{\mathbb{Q}}$ which, together with the images of $a$ and $b$, satisfies the project's predicate `IsKleinDatum`: explicitly, $\mathrm{kleinH}(u_0)^3(4a^3+27b^2)+6912\,a^3\,\mathrm{kleinV}(u_0)^5=0$ and $\mathrm{kleinV}(u_0)\neq 0$, where $\mathrm{kleinV}(u)=u(u^{10}+11u^5-1)$, $\mathrm{kleinH}$ and $\mathrm{kleinT}$ are the degree $20$ and degree $30$ Klein icosahedral forms. Let $W_1$ be a Weierstrass curve over $\mathbb{Q}$ whose base change to $\overline{\mathbb{Q}}$ equals the member `rsMember` of the Rubin–Silverberg family at parameter $t_0$, i.e. the curve $y^2=x^3+A x+B$ with $A=a\,\mathrm{kleinHHom}(n,d)/\mathrm{kleinH}(u_0)$, $B=b\,\mathrm{kleinTHom}(n,d)/\mathrm{kleinT}(u_0)$, where $n=(\mathrm{rsBeta}(u_0)+l u_0)t_0+u_0$ and $d=(\mathrm{rsGamma}(u_0)+l)t_0+1$ and $\mathrm{kleinHHom},\mathrm{kleinTHom}$ are the homogenisations of the Klein forms; assume $\Delta(W_1)\neq 0$. The conclusion asserts the existence of a $\mathbb{Z}/5$-linear isomorphism $\varphi$ from the $5$-torsion submodule $\{P : 5P=0\}$ of the group of affine points of $y^2=x^3+ax+b$ over $\overline{\mathbb{Q}}$ onto the corresponding $5$-torsion submodule of $W_1$ over $\overline{\mathbb{Q}}$, such that $\varphi(\sigma\cdot x)=\sigma\cdot\varphi(x)$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $5$-torsion point $x$; here the $\mathbb{Z}/5$-module structure and the action of $\sigma$ on points are the ones supplied by the project (the action induced by functoriality of the group of affine points). No nonsingularity hypothesis on $y^2=x^3+ax+b$ is imposed: it follows from the Klein datum condition.
--
--   This is the constancy statement in the Rubin–Silverberg construction of families of elliptic curves with constant mod $p$ representation, specialised to $p=5$ and to the Klein icosahedral parametrisation: all members of the family $t\mapsto$ `rsMember a b u₀ l t` have isomorphic mod $5$ Galois representations, and the statement here compares the fibre at an arbitrary rational $t_0$ with the fibre at $t=0$, which is $y^2=x^3+ax+b$. Unlike the textbook formulation it is phrased not in terms of representations of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ but as a $\mathbb{Z}/5$-linear isomorphism of $5$-torsion submodules of groups of affine points, equivariant for all $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$, and the relation between $W_1$ and the family member is imposed after base change to $\overline{\mathbb{Q}}$. It is the input used by [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists), which produces, from a semistable model with irreducible mod $5$ representation, an auxiliary curve with irreducible mod $3$ representation and the same mod $5$ representation — the $3$–$5$ switch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_exists_torsionBy_linearEquiv_rsMember.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point RubinSilverberg
open scoped Classical

theorem RubinSilverberg.exists_torsionBy_linearEquiv_rsMember (a b l t₀ : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (u₀ : AlgebraicClosure ℚ) (h₀ : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) a) (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀) (W₁ : WeierstrassCurve ℚ) (hW₁ : W₁.map (algebraMap ℚ (AlgebraicClosure ℚ)) = rsMember (algebraMap ℚ (AlgebraicClosure ℚ) a) (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) l) (algebraMap ℚ (AlgebraicClosure ℚ) t₀)) (hΔ₁ : W₁.Δ ≠ 0) : ∃ φ : Submodule.torsionBy ℤ ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point (5 : ℕ) ≃ₗ[ZMod 5] Submodule.torsionBy ℤ (W₁⁄(AlgebraicClosure ℚ)).Point (5 : ℕ), ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : Submodule.torsionBy ℤ ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℚ)⁄(AlgebraicClosure ℚ)).Point (5 : ℕ)), φ (σ • x) = σ • φ x := by sorry
