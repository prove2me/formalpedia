-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_full_rank_normalized_group_equations
-- name    : PhilipponMultiplicity.exists_full_rank_normalized_group_equations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-03T10:40:45.905013+00:00
-- url     : https://prove2.me/theorems/a4a99734-6924-4996-bef5-629f1d59d468
-- title:
--   Full-rank polynomial equations for a normalized group neighborhood
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero, and let $G$ be a finite product of embedded commutative algebraic groups. If the projective blocks have dimensions $n_i$, write
--   $$A=\prod_i K^{n_i+1}$$
--   for their homogeneous coordinate tuples. There exist an integer $r\geq0$, one pivot $c_i$ in each block, a tuple $a\in A$, and polynomials $P_1,\ldots,P_r,H\in K[A]$ satisfying the following conditions.
--
--   The tuple $a$ is a normalized representative of the identity, belongs to the principal open set, and satisfies all equations:
--   $$a_{i,c_i}=1,\qquad [a_i]=0_i,\qquad H(a)\ne0,\qquad P_j(a)=0.$$
--   The formal Jacobian at $a$ has full row rank. Equivalently, the linear map
--   $$J_a:A\longrightarrow K^r,\qquad J_a(v)_j=\sum_{\nu}\frac{\partial P_j}{\partial X_\nu}(a)v_\nu$$
--   is surjective.
--
--   The equations give exactly the original group in normalized coordinates on the chosen principal open: for every $v\in A$ with $H(v)\ne0$,
--   $$P_1(v)=\cdots=P_r(v)=0$$
--   if and only if all pivot coordinates of $v$ equal one and there is a point $x\in G(K)$ with $[v_i]=x_i$ in every block. The pivots ensure that these representatives are nonzero.
--
--   This is the smooth local-equation theorem at the group identity in the given embedding. All derivatives in the statement are formal polynomial partial derivatives. No norm, analytic derivative, complementary projection, or analytic chart is assumed; disconnected groups are allowed.
--
--   **Formalization Note.** The geometric reduction proves regularity of the actual homogeneous cone over algebraically closed fields, identifies a principal-open cone neighborhood with genuine group representatives, and appends the normalization equations using the blockwise Euler identity. The sole remaining input is the general [regular-point affine Jacobian criterion](https://prove2.me/theorems/78858b9c-2b78-4629-ac8b-79b53b52d14a), which contains no group, projective, or analytic data. The original formal statement is unchanged.
-- source:
--   V. Platonov and A. Rapinchuk, Algebraic Groups and Number Theory (1994), section 2.4.3, Proposition 2.22, printed pp.97--98, and the following paragraph on smoothness of homogeneous varieties and algebraic groups, https://uva.theopenscholar.com/files/andrei-rapinchuk/files/agnt_english.pdf . The present statement specializes the full-rank local equations to the normalized affine coordinates of the given embedded group. Refining the ambient open to a principal open and identifying the actual carrier are included in the Open obligation. For the Jacobian formulation also see T. Q. Pham, Weil's Conjecture on Tamagawa Number, section 5.3, Definition 81, printed p.32, https://toanqpham.github.io/Tamagawa.pdf . For characteristic-zero group smoothness in scheme language see Stacks Project, Lemma 39.8.2, Tag 047N, https://stacks.math.columbia.edu/tag/047N . This is an algebraic statement over algebraically closed characteristic-zero fields; it makes no local-compactness or analytic-coordinate assumption.

import Definitions.Def_PhilipponMultiplicity_Geometry
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem exists_full_rank_normalized_group_equations
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (G : EmbeddedGroupProduct K) :
    ∃ (r : ℕ)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (a : G.ambient.Variable → K)
      (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing),
      (∀ i, a ⟨i, c i⟩ = 1) ∧
      (∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i) ∧
      MvPolynomial.eval a H ≠ 0 ∧
      (∀ i, MvPolynomial.eval a (P i) = 0) ∧
      Function.Surjective (fun v : G.ambient.Variable → K => fun i : Fin r =>
        ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (P i)) * v j) ∧
      (∀ v : G.ambient.Variable → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ((∀ i, v ⟨i, c i⟩ = 1) ∧
            ∃ x : G.Point, ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
              Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i))) := by sorry

end PhilipponMultiplicity
