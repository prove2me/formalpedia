-- Prove2me | Theorems.Thm_WeierstrassCurve_mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul
-- name    : WeierstrassCurve.mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/7b2524b2-5482-5a28-aa13-46652e277257
-- title:
--   Descent of Frobenius-equivariant homomorphisms to a finite field
-- statement:
--   Let $F$ be a finite field, $k$ an algebraically closed field which is an $F$-algebra, and $W_1, W_2$ Weierstrass curves over $F$, both elliptic. Let $\sigma : k \simeq_{\mathrm{alg}[F]} k$ be an $F$-algebra automorphism of $k$ satisfying $\sigma(x) = x^{\#F}$ for every $x \in k$, and let $\beta$ be an additive homomorphism from the group of points of the affine curve $W_1$ base changed to $k$ to that of $W_2$ base changed to $k$. Assume (i) $\beta \in$ [`WeierstrassCurve.rationalHomSet k (W₁.baseChange k) (W₂.baseChange k)`](def/WeierstrassCurve_RationalEnd.html#L28), that is, either $\beta = 0$ or there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ with coefficients in $k$ and a finite set $B \subseteq k$ such that for every nonsingular affine point $(x,y)$ of $W_1$ over $k$ with $x \notin B$ the values of $d_X$ and $d_Y$ at $(x,y)$ are nonzero and $\beta(x,y) = (n_X/d_X,\, n_Y/d_Y)(x,y)$; and (ii) $\beta(\sigma \cdot P) = \sigma \cdot \beta(P)$ for all points $P$ of $W_1$ over $k$, for the coordinatewise action of $\sigma$. Then $\beta \in$ [`WeierstrassCurve.rationalHomSet k W₁ W₂`](def/WeierstrassCurve_RationalEnd.html#L28): either $\beta = 0$, or the same description holds with the four representing polynomials having coefficients in $F$.
--
--   This is Galois descent for homomorphisms of elliptic curves over a finite field in the elementary form used here: a homomorphism on $k$-points given by rational formulae over $k$ and commuting with the $\#F$-power Frobenius is already given by rational formulae over $F$. It feeds [`WeierstrassCurve.rationalEndSubring_baseChange_eq_of_frobenius_eq_smul`](thm.html#WeierstrassCurve.rationalEndSubring_baseChange_eq_of_frobenius_eq_smul), which identifies the endomorphisms over $F$ inside the geometric endomorphisms as the Frobenius-commuting ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.mem_rationalHomSet_of_mem_rationalHomSet_baseChange_of_forall_apply_smul {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) {β : (W₁⁄k).Point →+ (W₂⁄k).Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k (W₁.baseChange k) (W₂.baseChange k)) (hcomm : ∀ P : (W₁⁄k).Point, β (σ • P) = σ • β P) : β ∈ WeierstrassCurve.rationalHomSet k W₁ W₂ := by sorry
