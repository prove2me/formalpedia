-- Prove2me | Theorems.Thm_WeierstrassCurve_galoisRepIsIrreducible_three_of_forall_eval_Psi3_ne_zero
-- name    : WeierstrassCurve.galoisRepIsIrreducible_three_of_forall_eval_Psi3_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/2bfb2e06-d52b-51d4-b183-8dd35e9ecb9f
-- title:
--   Mod-3 irreducibility from Ψ₃ with no rational root
-- statement:
--   Let $V$ be a Weierstrass equation over $\mathbb{Q}$ (a term of `WeierstrassCurve ℚ`, so given by its coefficients $a_1,\dots,a_6$) whose discriminant satisfies $V.\Delta \ne 0$, and suppose that the $3$-division polynomial `V.Ψ₃` $\in \mathbb{Q}[X]$ has no rational root, i.e. $\Psi_3(x) \ne 0$ for every $x \in \mathbb{Q}$. The conclusion is the project's predicate `Affine.Point.GaloisRepIsIrreducible ℚ V 3` taken with $K$ the field `AlgebraicClosure ℚ`, which by definition is the conjunction of two assertions about $M :=$ `Submodule.torsionBy ℤ (V⁄(AlgebraicClosure ℚ)).Point 3`, the $3$-torsion of the group of affine points of the base change of $V$ to an algebraic closure of $\mathbb{Q}$, regarded as a module over `ZMod 3` through the project's instance: first, that $M$ is nontrivial (it has at least two elements); and second, that every `ZMod 3`-submodule $N$ of $M$ which is `IsGaloisStable ℚ`, i.e. satisfies $\sigma \cdot x \in N$ for all $x \in N$ and all $\mathbb{Q}$-algebra automorphisms $\sigma$ of `AlgebraicClosure ℚ` (the action being $P \mapsto$ `Point.map σ.toAlgHom P` on points), equals $\bot$ or $\top$. Thus irreducibility is formulated purely as the absence of proper nonzero submodules stable under the abstract group of $\mathbb{Q}$-algebra automorphisms of the chosen algebraic closure; no topology on the Galois group, no Galois module structure beyond this action, and no statement about associated representations or about rational $3$-isogenies is part of the Lean assertion.
--
--   This is the standard dictionary between rational roots of the $3$-division polynomial and the existence of a Galois-stable line in $E[3]$: if $\Psi_3$ has no rational root then $E$ has no rational subgroup of order $3$, so $\bar\rho_{E,3}$ is irreducible. The Lean version is stated for a Weierstrass equation with nonvanishing discriminant rather than for an elliptic curve, and irreducibility is phrased as the submodule condition of the project's `GaloisRepIsIrreducible` over a fixed algebraic closure of $\mathbb{Q}$; the converse (stability forces a rational root) appears only inside the proof. It serves as the irreducibility certificate in the $3$–$5$ switch: [`WeierstrassCurve.threeFiveAuxiliaryCurveExists`](thm.html#WeierstrassCurve.threeFiveAuxiliaryCurveExists) picks a member of an explicit family with prescribed $5$-torsion for which the $3$-division polynomial has no rational root, and uses this theorem to conclude that the member's mod-$3$ representation is irreducible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_galoisRepIsIrreducible_three_of_forall_eval_Psi3_ne_zero.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.galoisRepIsIrreducible_three_of_forall_eval_Psi3_ne_zero (V : WeierstrassCurve ℚ) (hΔ : V.Δ ≠ 0) (h : ∀ x : ℚ, V.Ψ₃.eval x ≠ 0) : Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ V 3 := by sorry
