-- Prove2me | Theorems.Thm_WeierstrassCurve_threeFiveAuxiliaryCurveExists
-- name    : WeierstrassCurve.threeFiveAuxiliaryCurveExists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/6e0c9e2a-faca-5b2c-bf56-bb7d8215703d
-- title:
--   Auxiliary curve for the 3–5 switch
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ whose discriminant $\Delta$ is nonzero, which is a semistable model in the project's sense that no prime $p$ with $p \mid \Delta$ also divides $c_4$, and which satisfies the project's predicate `ModRepIsIrreducible` at $5$: taking $W$ over $\mathbb{Q}$ and forming the $5$-torsion submodule $\{P : 5P = 0\}$ of the group of affine points over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, that $\mathbb{Z}/5$-module is nontrivial and its only submodules stable under the action of all $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ are $\bot$ and $\top$. Then there exists a Weierstrass curve $W'$ over $\mathbb{Z}$ such that: $W'$ has nonzero discriminant; $W'$ is again a semistable model in the same sense (no prime divides both $\Delta(W')$ and $c_4(W')$); $W'$ satisfies `ModRepIsIrreducible` at $3$, i.e. the $3$-torsion of $W'$ over the algebraic closure is nontrivial with no proper nonzero Galois-stable $\mathbb{Z}/3$-submodule; and there is a $\mathbb{Z}/5$-linear isomorphism $\varphi$ from the $5$-torsion of $W$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ onto the $5$-torsion of $W'$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ satisfying $\varphi(\sigma \cdot x) = \sigma \cdot \varphi(x)$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of the algebraic closure and every $5$-torsion point $x$, the action being the coordinatewise action on points. No symplectic or determinant condition on $\varphi$ is imposed, so the isomorphism asserted is weaker than the one Rubin–Silverberg's families provide; irreducibility of the mod-$5$ representation of $W'$ is not stated separately, being a consequence of $\varphi$ and the hypothesis on $W$.
--
--   This is the auxiliary-curve step of Wiles's 3–5 switch, Lemma 3.49 of Darmon–Diamond–Taylor, in the form: from a semistable integral model with irreducible mod-$5$ representation one produces a second semistable integral model with irreducible mod-$3$ representation and with Galois-isomorphic $5$-torsion. Compared with the textbook statement, everything is phrased for integral Weierstrass models and the project's semistability condition on $(\Delta, c_4)$ rather than for elliptic curves and their conductors, and the $5$-torsion isomorphism is only required to be $\mathbb{Z}/5$-linear and equivariant, not symplectic. It is used to prove [`WeierstrassCurve.threeFiveSwitchCurve`](thm.html#WeierstrassCurve.threeFiveSwitchCurve), where the equivariant isomorphism of $5$-torsion is converted into the congruence $5 \mid a_\ell(W') - a_\ell(W)$ at primes $\ell \neq 5$ good for both models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_threeFiveAuxiliaryCurveExists.lean

import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.threeFiveAuxiliaryCurveExists (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (h5 : W.ModRepIsIrreducible 5) : ∃ W' : WeierstrassCurve ℤ, W'.Δ ≠ 0 ∧ W'.IsSemistableModel ∧ W'.ModRepIsIrreducible 3 ∧ ∃ φ : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (5 : ℕ) ≃ₗ[ZMod 5] Submodule.torsionBy ℤ ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (5 : ℕ), ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (5 : ℕ)), φ (σ • x) = σ • φ x := by sorry
