-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_reduction_inZeroComponentAt
-- name    : WeierstrassCurve.exists_reduction_inZeroComponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/1dc6e2ec-23ca-55ab-865e-38e06aa17702
-- title:
--   Reduction map to the special fibre at a place of ℚ̄
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $A$ be a valuation subring of $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, with residue field $k_A =$ `IsLocalRing.ResidueField A` and residue map $P \mapsto \bar P$. Write $E$ for the group of points of the affine Weierstrass curve obtained from $W$ by base change to $\mathbb{Q}$ and then to $\bar{\mathbb{Q}}$, and $\bar W$ for the affine Weierstrass curve obtained from $W$ by reducing its coefficients into $k_A$. The assertion is that there exists a map $\mathrm{red} : E \to \bar W(k_A)$ (into the point group of the affine curve $\bar W$, i.e. the point at infinity together with the nonsingular affine $k_A$-points of $\bar W$) such that: (i) $\mathrm{red}(0) = 0$; (ii) $\mathrm{red}(P+Q) = \mathrm{red}(P) + \mathrm{red}(Q)$ whenever $P$ and $Q$ both satisfy `W.InZeroComponentAt A`, that is, each is either $0$ or of the form $(x,y)$ with $x \notin A$, or of the form $(x,y)$ with $x, y \in A$ and $(\bar x, \bar y)$ nonsingular on $\bar W$; (iii) for every nonsingular affine point $(x,y)$ of $E$ with $x, y \in A$ and $(\bar x,\bar y)$ nonsingular on $\bar W$, $\mathrm{red}(x,y) = (\bar x, \bar y)$; (iv) $\mathrm{red}(x,y) = 0$ whenever $x \notin A$; (v) if $P$ satisfies `W.InZeroComponentAt A` and $\mathrm{red}(P) = 0$ then $P = 0$ or $P = (x,y)$ with $x \notin A$; and (vi) $\mathrm{red}(\sigma \bullet P) = \mathrm{red}(P)$ for every $P \in E$ and every $\sigma$ in `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Aut}_{\mathbb{Q}}(\bar{\mathbb{Q}})$ of the inertia subgroup of the decomposition subgroup of $A$ over $\mathbb{Q}$.
--
--   This is the reduction homomorphism on the zero component of an elliptic curve at a place of $\bar{\mathbb{Q}}$, with kernel the points of non-integral abscissa (the kernel of reduction), stated without any hypothesis on the special fibre, which may be singular. It is the tool used in this development to study the Galois action on torsion at a place, in particular in the results on torsion subgroups not meeting the zero component and on the behaviour of torsion of order the residue characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_reduction_inZeroComponentAt.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_reduction_inZeroComponentAt (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (IsLocalRing.ResidueField A)] : ∃ red : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point → (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Point, red 0 = 0 ∧ (∀ P Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, W.InZeroComponentAt A P → W.InZeroComponentAt A Q → red (P + Q) = red P + red Q) ∧ (∀ (x y : AlgebraicClosure ℚ) (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y) (hx : x ∈ A) (hy : y ∈ A) (hns : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩)), red (Point.some x y h) = Point.some (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩) hns) ∧ (∀ (x y : AlgebraicClosure ℚ) (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y), x ∉ A → red (Point.some x y h) = 0) ∧ (∀ P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, W.InZeroComponentAt A P → red P = 0 → P = 0 ∨ ∃ (x y : AlgebraicClosure ℚ) (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y), P = Point.some x y h ∧ x ∉ A) ∧ (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, red (σ • P) = red P) := by sorry
