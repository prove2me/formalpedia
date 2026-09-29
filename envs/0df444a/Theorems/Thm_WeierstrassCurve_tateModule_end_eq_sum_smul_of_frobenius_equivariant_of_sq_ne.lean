-- Prove2me | Theorems.Thm_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne
-- name    : WeierstrassCurve.tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/55a611a6-5b28-557b-b4c6-5d0327bb3a99
-- title:
--   Tate's theorem for T_ℓ: non-scalar Frobenius case
-- statement:
--   Let $F$ be a finite field, $k$ an algebraically closed field with an $F$-algebra structure, and $W$ a Weierstrass curve over $F$ that is elliptic. Let $\sigma : k \simeq_{\mathrm{alg}[F]} k$ be an $F$-algebra automorphism of $k$ acting by $\sigma x = x^{\#F}$ on every $x \in k$, and let $\ell$ be a prime with $\ell \neq 0$ in $F$. Write $q = \#F$ and $t = q + 1 - \#W(F)$, where $\#W(F)$ is the cardinality of the point group of the affine model of $W$ over $F$, and assume $t^2 \neq 4q$. Here [`TateModule ℓ M`](def/EllipticCurve_TateModule.html#L15) denotes the additive subgroup of sequences $x : \mathbb{N} \to M$ satisfying $\ell^n \cdot x(n) = 0$ and $\ell \cdot x(n+1) = x(n)$ for all $n$, a $\mathbb{Z}_\ell$-module, and [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) sends a group element to the endomorphism acting on such a sequence termwise; the relevant module is the Tate module of the point group of the base change $W \!\!\mathbin{/}\!\! k$, with $\sigma$ acting through the Galois action. Let $\Phi$ be a $\mathbb{Z}_\ell$-linear endomorphism of this Tate module commuting with the operator attached to $\sigma$. The conclusion asserts the existence of a natural number $m$, additive endomorphisms $\alpha_j$ of the point group of $W \!\!\mathbin{/}\!\! k$, scalars $c_j \in \mathbb{Z}_\ell$ and $\mathbb{Z}_\ell$-linear endomorphisms $\Psi_j$ of the Tate module, indexed by $j \in \mathrm{Fin}\,m$, such that: each $\alpha_j$ lies in [`WeierstrassCurve.rationalHomSet k W W`](def/WeierstrassCurve_RationalEnd.html#L28), i.e. is either zero or rationally represented, meaning there are $n_X, d_X, n_Y, d_Y \in F[X][Y]$ and a finite set $B \subseteq k$ with $d_X, d_Y$ non-vanishing and $\alpha_j(x,y) = (n_X/d_X, n_Y/d_Y)$ (evaluated at $(x,y)$ after base change) for every nonsingular affine point $(x,y)$ with $x \notin B$; each $\Psi_j$ acts on a Tate-module element termwise by $\alpha_j$, that is $(\Psi_j x)(n) = \alpha_j(x(n))$ for all $n$; and $\Phi = \sum_j c_j \Psi_j$.
--
--   This is the surjectivity half of Tate's theorem for an elliptic curve over a finite field, $\mathrm{End}_F(W) \otimes \mathbb{Z}_\ell \to \mathrm{End}_{\mathbb{Z}_\ell[\sigma]}(T_\ell W)$, in the case where the hypothesis $t^2 \neq 4q$ forces the matrix of Frobenius on $T_\ell W$ to be non-scalar; the proof cites the Hasse–Weil identities $\operatorname{tr}(\sigma \mid T_\ell W) = q + 1 - \#W(F)$ and $\det(\sigma \mid T_\ell W) = q$ together with divisibility and additivity properties of rational homomorphisms. It feeds the identification of $\mathbb{Z}_\ell \otimes \mathrm{End}$ with a matrix algebra used downstream in the analysis of residual representations attached to elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.tateModule_end_eq_sum_smul_of_frobenius_equivariant_of_sq_ne {F : Type*} [Field F] [Fintype F] {k : Type} [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : F) ≠ 0) (ht : ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≠ 4 * (Fintype.card F : ℤ)) (Φ : TateModule ℓ (W⁄k).Point →ₗ[ℤ_[ℓ]] TateModule ℓ (W⁄k).Point) (hΦ : Φ ∘ₗ TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ = TateModule.rep ℓ (W⁄k).Point (k ≃ₐ[F] k) σ ∘ₗ Φ) : ∃ (m : ℕ) (α : Fin m → ((W⁄k).Point →+ (W⁄k).Point)) (c : Fin m → ℤ_[ℓ]) (Ψ : Fin m → (TateModule ℓ (W⁄k).Point →ₗ[ℤ_[ℓ]] TateModule ℓ (W⁄k).Point)), (∀ j, α j ∈ WeierstrassCurve.rationalHomSet k W W) ∧ (∀ j (x : TateModule ℓ (W⁄k).Point) (n : ℕ), ((Ψ j x : TateModule ℓ (W⁄k).Point) : ℕ → (W⁄k).Point) n = α j ((x : ℕ → (W⁄k).Point) n)) ∧ Φ = ∑ j, c j • Ψ j := by sorry
