-- Prove2me | Theorems.Thm_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_eq
-- name    : WeierstrassCurve.tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/42beb15c-0b6b-5c04-a363-bd7599d3046b
-- title:
--   Tate's theorem for T_ℓ when t²=4q
-- statement:
--   Let $F$ be a finite field, $k$ an algebraically closed field which is an $F$-algebra and algebraic over $F$, and let $W$ be a Weierstrass curve over $F$ that is elliptic. Let $\sigma$ be an $F$-algebra automorphism of $k$ with $\sigma x = x^{\#F}$ for all $x \in k$, let $\ell$ be a prime with $\ell \neq 0$ in $F$, and assume the integer $t := \#F + 1 - \#W(F)$, where $\#W(F)$ is the cardinality of the affine point group of $W$ over $F$, satisfies $t^2 = 4\,\#F$. Here [`TateModule ℓ (W⁄k).Point`](def/EllipticCurve_TateModule.html#L15) is the additive group of sequences $(x_n)$ of points of $W$ over $k$ with $\ell^n x_n = 0$ and $\ell\, x_{n+1} = x_n$, a $\mathbb{Z}_\ell$-module, and [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) sends a group element to the endomorphism acting on each component. Then for every $\mathbb{Z}_\ell$-linear endomorphism $\Phi$ of this Tate module commuting with the endomorphism attached to $\sigma$, there are $m \in \mathbb{N}$, additive endomorphisms $\alpha_j$ of the point group of $W$ over $k$ lying in `rationalHomSet k W W` (that is, each $\alpha_j$ is zero or is given, off a finite exceptional set of $x$-coordinates, by ratios $n_X/d_X$, $n_Y/d_Y$ of bivariate polynomials over $F$ evaluated at the coordinates), scalars $c_j \in \mathbb{Z}_\ell$, and $\mathbb{Z}_\ell$-linear endomorphisms $\Psi_j$ of the Tate module acting componentwise by $\alpha_j$, with $\Phi = \sum_j c_j \Psi_j$.
--
--   This is the surjectivity half of Tate's theorem on endomorphisms of an elliptic curve over a finite field, in the case where the trace of Frobenius satisfies $t^2 = 4q$ (so that Frobenius acts on the Tate module as the scalar $t/2$ and the curve is of Deuring's supersingular type with $\operatorname{End}_F(W)$ a maximal order in a quaternion algebra): every $\mathbb{Z}_\ell$-linear endomorphism of $T_\ell W$ commuting with Frobenius is a $\mathbb{Z}_\ell$-combination of endomorphisms induced by $F$-rational endomorphisms of $W$. It feeds the identification of $\mathbb{Z}_\ell \otimes \operatorname{End}_F(W)$ with a matrix algebra used in [`WeierstrassCurve.nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix`](thm.html#WeierstrassCurve.nonempty_padicInt_tensorProduct_rationalEndSubring_algEquiv_matrix).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_eq {F : Type*} [Field F] [Fintype F] {k : Type} [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] [Algebra.IsAlgebraic F k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : F) ≠ 0) (ht : ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 = 4 * (Fintype.card F : ℤ)) (Φ : TateModule ℓ (W⁄k).Point →ₗ[ℤ_[ℓ]] TateModule ℓ (W⁄k).Point) (hΦ : Φ ∘ₗ TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ = TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ ∘ₗ Φ) : ∃ (m : ℕ) (α : Fin m → ((W⁄k).Point →+ (W⁄k).Point)) (c : Fin m → ℤ_[ℓ]) (Ψ : Fin m → (TateModule ℓ (W⁄k).Point →ₗ[ℤ_[ℓ]] TateModule ℓ (W⁄k).Point)), (∀ j, α j ∈ WeierstrassCurve.rationalHomSet k W W) ∧ (∀ j (x : TateModule ℓ (W⁄k).Point) (n : ℕ), ((Ψ j x : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n = α j ((x : ℕ → (W⁄k).Point) n)) ∧ Φ = ∑ j, c j • Ψ j := by sorry
