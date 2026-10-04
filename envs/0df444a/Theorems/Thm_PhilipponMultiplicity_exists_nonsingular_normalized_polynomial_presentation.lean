-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_nonsingular_normalized_polynomial_presentation
-- name    : PhilipponMultiplicity.exists_nonsingular_normalized_polynomial_presentation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-03T09:31:54.015981+00:00
-- url     : https://prove2.me/theorems/26ef4e3a-97d2-4ca0-bbfe-7f1f05265761
-- title:
--   A nonsingular polynomial presentation in normalized group coordinates
-- statement:
--   Let $K$ be a Philippon base field, isometrically isomorphic to $\mathbb C$ or to a completed algebraic closure $\mathbb C_p$. Let $G$ be a finite product of embedded commutative algebraic groups. Write $I$ for the projective blocks, $n_i$ for their ambient dimensions, and
--   $$A=\prod_{i\in I}K^{n_i+1}.$$
--   There exist nonnegative integers $d,r$, a pivot $c_i$ in each block, a normalized representative $a\in A$ of the group identity, polynomials
--   $$P_1,\ldots,P_r,H\in K[A],$$
--   a continuous linear map $\rho:A\to K^d$, and a continuous linear isomorphism
--   $$L:A\xrightarrow{\sim}K^r\times K^d$$
--   with the following properties.
--
--   1. The chosen point belongs to the principal open set and satisfies the equations:
--
--      $$a_{i,c_i}=1,\qquad [a_i]=0_i,\qquad H(a)\ne0,\qquad P_j(a)=0.$$
--
--   2. The augmented polynomial map has the invertible derivative $L$ at $a$:
--
--      $$F(v)=\bigl((P_j(v))_{j=1}^r,\rho(v-a)\bigr),\qquad DF(a)=L.$$
--
--   3. On the principal open set defined by $H$, the equations describe precisely the normalized tuples representing actual group points. For every $v\in A$ with $H(v)\ne0$,
--
--      $$P_1(v)=\cdots=P_r(v)=0$$
--
--      holds if and only if every pivot coordinate of $v$ is one and there exists $x\in G(K)$ such that each (necessarily nonzero) projective block of $v$ represents the corresponding block of $x$.
--
--   This is a local nonsingular presentation of the given embedded group in its original normalized coordinates. The polynomials are affine-coordinate polynomials and are not required to be homogeneous. The existence of $L$ incorporates the dimension equality between the ambient space and $K^r\times K^d$. No connectedness or positive dimension is assumed.
--
--   **Formalization Note.** The analytic derivative and complementary continuous linear coordinates are constructed from the formal polynomial Jacobian. The remaining geometric existence statement is [full-rank equations in normalized group coordinates](https://prove2.me/theorems/a4a99734-6924-4996-bef5-629f1d59d468), over algebraically closed fields of characteristic zero; it remains Open. The original formal statement and its base-field hypothesis are unchanged.
-- source:
--   V. Platonov and A. Rapinchuk, Algebraic Groups and Number Theory (1994), section 3.1, printed p.111, the local-equation and complementary-coordinate construction immediately following Theorem 3.2 (using Proposition 2.22), https://uva.theopenscholar.com/files/andrei-rapinchuk/files/agnt_english.pdf . See also T. Q. Pham, Weil's Conjecture on Tamagawa Number, section 5.3, Definition 81 and Proposition 84, printed p.32, https://toanqpham.github.io/Tamagawa.pdf . This auxiliary statement asks for the algebraic smooth presentation at the identity in the actual normalized embedding, together with an invertible augmented polynomial Jacobian. It does not import the locally compact field restriction of Platonov--Rapinchuk into the C_p case, and does not assert the resulting analytic chart. Smoothness, the principal-open comparison with the given carrier, and the Jacobian certificate remain to be established.

import Definitions.Def_PhilipponMultiplicity_Geometry
set_option autoImplicit false
open Filter Topology

namespace PhilipponMultiplicity

theorem exists_nonsingular_normalized_polynomial_presentation
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) :
    ∃ (d r : ℕ)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (a : G.ambient.Variable → K)
      (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing)
      (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K))
      (L : (G.ambient.Variable → K) ≃L[K] ((Fin r → K) × (Fin d → K))),
      (∀ i, a ⟨i, c i⟩ = 1) ∧
      (∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i) ∧
      MvPolynomial.eval a H ≠ 0 ∧
      (∀ i, MvPolynomial.eval a (P i) = 0) ∧
      HasFDerivAt
        (fun v : G.ambient.Variable → K =>
          ((fun i => MvPolynomial.eval v (P i)), ρ (v-a)))
        (L : (G.ambient.Variable → K) →L[K] ((Fin r → K) × (Fin d → K))) a ∧
      (∀ v : G.ambient.Variable → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ((∀ i, v ⟨i, c i⟩ = 1) ∧
            ∃ x : G.Point, ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
              Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i))) := by sorry

end PhilipponMultiplicity
