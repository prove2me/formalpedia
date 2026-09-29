-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples
-- name    : WeierstrassCurve.exists_rational_separable_isogeny_of_map_mem_zmultiples
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/6550a1bc-3eb3-5865-8b33-3d7abfcb72d7
-- title:
--   Frobenius-stable ℓ-torsion subgroup as an F-rational isogeny kernel
-- statement:
--   Let $F$ be a finite field, $k$ a field which is an $F$-algebra, and $W$ a Weierstrass curve over $F$ which is elliptic (invertible discriminant). Let $\sigma : k \to k$ be an $F$-algebra endomorphism with $\sigma(x) = x^{\#F}$ for all $x \in k$, let $\ell$ be a prime with $\ell \neq 2$ and $\ell \neq 0$ in $F$, and let $Q$ be a point of the affine curve $W_{k} = W \times_F k$ of exact additive order $\ell$ whose image under the map on points induced by $\sigma$ lies in the subgroup $\langle Q \rangle$ of integer multiples of $Q$. Then there exist a Weierstrass curve $V$ over $F$, again elliptic, and a homomorphism of additive groups $\varphi : W_k(k) \to V_k(k)$ between the groups of affine points, whose kernel is exactly $\langle Q \rangle$, together with polynomials $P, S, N_0, N_1, R \in F[X]$ and a finite set $B \subseteq k$ such that $P$ is monic, $\deg P = \deg S + 1$, $P$ and $S$ are coprime in $F[X]$, and for every pair $(x,y) \in k^2$ which is a nonsingular point of $W_k$ with $x \notin B$ one has $S(x) \neq 0$, $R(x) \neq 0$ and
--   $$\varphi(x,y) = \Bigl(\frac{P(x)}{S(x)},\ \frac{N_0(x) + N_1(x)\,y}{R(x)}\Bigr).$$
--   Nothing is asserted about the behaviour of $\varphi$ at abscissae lying in $B$, nor about the degree of $\varphi$ beyond the relation $\deg P = \deg S + 1$.
--
--   This is Vélu's quotient isogeny $W \to W/\langle Q\rangle$ for a cyclic subgroup of odd prime order, combined with descent of the quotient curve and of the isogeny formulae to the finite base field $F$, the point being that stability of $\langle Q \rangle$ under the $\#F$-power Frobenius forces the symmetric functions entering Vélu's formulae to be $F$-rational. It feeds [`WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_zmultiples_of_map_mem_zmultiples`](thm.html#WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_zmultiples_of_map_mem_zmultiples), where such an isogeny is produced as an element of the set of $F$-rational homomorphisms with prescribed kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_rational_separable_isogeny_of_map_mem_zmultiples.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem WeierstrassCurve.exists_rational_separable_isogeny_of_map_mem_zmultiples
    {F : Type*} [Field F] [Fintype F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (σ : k →ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓF : (ℓ : F) ≠ 0)
    (Q : (W.baseChange k).toAffine.Point) (hQ : addOrderOf Q = ℓ)
    (hσQ : WeierstrassCurve.Affine.Point.map (W' := W) σ Q ∈ AddSubgroup.zmultiples Q) :
    ∃ V : WeierstrassCurve F, V.IsElliptic ∧
      ∃ φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point,
        φ.ker = AddSubgroup.zmultiples Q ∧
        ∃ (P S N₀ N₁ R : F[X]) (B : Set k), P.Monic ∧ P.natDegree = S.natDegree + 1 ∧
          IsCoprime P S ∧ B.Finite ∧
          ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
            aeval x S ≠ 0 ∧ aeval x R ≠ 0 ∧
            ∃ h', φ (.some x y h) =
              .some (aeval x P / aeval x S) ((aeval x N₀ + aeval x N₁ * y) / aeval x R) h' := by sorry
