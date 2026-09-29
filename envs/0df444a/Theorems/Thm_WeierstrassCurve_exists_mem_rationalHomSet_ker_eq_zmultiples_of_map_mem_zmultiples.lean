-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_zmultiples_of_map_mem_zmultiples
-- name    : WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_zmultiples_of_map_mem_zmultiples
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/9ebff230-9fd8-5ece-af81-77b18101f4c8
-- title:
--   Rational isogeny with rational dual killing a Frobenius-stable ℓ-subgroup
-- statement:
--   Let $F$ be a finite field, let $k$ be an algebraically closed field that is an $F$-algebra and algebraic over $F$, and let $W$ be a Weierstrass curve over $F$ satisfying `IsElliptic`. Let $\sigma : k \to k$ be an $F$-algebra map with $\sigma x = x^{|F|}$ for all $x \in k$, let $\ell$ be a prime with $\ell \neq 2$ whose image in $F$ is nonzero, and let $Q$ be a point of the affine curve obtained from $W$ by base change to $k$, of additive order exactly $\ell$, such that the image of $Q$ under the map induced by $\sigma$ lies in the subgroup $\langle Q\rangle$ of integer multiples of $Q$. The conclusion asserts the existence of a Weierstrass curve $V$ over $F$ satisfying `IsElliptic`, of an additive map $\varphi$ from the $k$-points of $W$ to those of $V$ and of an additive map $\psi$ back, both lying in the corresponding sets `rationalHomSet`, i.e. each is either zero or admits a representation by four bivariate polynomials $nX, dX, nY, dY \in F[X][Y]$ and a finite exceptional set $B \subseteq k$ such that for every nonsingular affine point $(x,y)$ with $x \notin B$ the two denominators are nonzero at $(x,y)$ and the map sends $(x,y)$ to $(nX/dX,\, nY/dY)$ evaluated there; moreover the kernel of $\varphi$ is exactly $\langle Q\rangle$, and $(\varphi,\psi)$ is a dual pair for $\ell$, meaning $\psi(\varphi(a)) = \ell\, a$ for all $a$ and $\varphi(\psi(b)) = \ell\, b$ for all $b$.
--
--   This is the existence, over the ground field $F$, of the quotient isogeny $W \to W/\langle Q\rangle$ attached to a Frobenius-stable cyclic subgroup of odd prime order, together with its dual isogeny, in the form of rationally represented homomorphisms on $k$-points. It feeds the construction of pairs of isogenies whose composites with Frobenius differ, used in the analysis of $\ell$-torsion of elliptic curves over finite fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_zmultiples_of_map_mem_zmultiples.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_zmultiples_of_map_mem_zmultiples {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] [Algebra.IsAlgebraic F k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓF : (ℓ : F) ≠ 0) (Q : (W.baseChange k).toAffine.Point) (hQ : addOrderOf Q = ℓ) (hσQ : WeierstrassCurve.Affine.Point.map (W' := W) σ Q ∈ AddSubgroup.zmultiples Q) : ∃ V : WeierstrassCurve F, V.IsElliptic ∧ ∃ φ ∈ WeierstrassCurve.rationalHomSet k W V, ∃ ψ ∈ WeierstrassCurve.rationalHomSet k V W, φ.ker = AddSubgroup.zmultiples Q ∧ AddMonoidHom.IsDualPair φ ψ (ℓ : ℤ) := by sorry
