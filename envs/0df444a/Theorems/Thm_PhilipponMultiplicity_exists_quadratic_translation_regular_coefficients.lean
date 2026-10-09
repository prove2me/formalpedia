-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_quadratic_translation_regular_coefficients
-- name    : PhilipponMultiplicity.exists_quadratic_translation_regular_coefficients
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-05T19:11:50.485452+00:00
-- url     : https://prove2.me/theorems/932d234f-b8dd-426a-9dcb-943463e17690
-- title:
--   Quadratic translation families with locally regular parameter coefficients
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $E$ be a connected commutative algebraic group with the given locally closed projective embedding. There are a projective realization $F\subseteq\mathbf P^N$ and an algebraic group isomorphism $E\to F$ regular in both directions with the following property.
--
--   Every pair $(x,y)\in F\times F$ lies in a Zariski-open neighborhood $U$ with fixed nonvanishing chart coordinates $X_{c_0}$ and $Y_{c_1}$. Write $\widehat X=X/X_{c_0}$ and $\widehat Y=Y/Y_{c_1}$. There are polynomials
--   $$
--   P_t(X)=\sum_m f_{tm}X^m\quad(0\le t\le N)
--   $$
--   with coefficient functions $f_{tm}:F\times F\to K$, each of total degree at most two in $X$, such that the following hold.
--
--   For each coefficient in the support of $P_t$ and every $a\in U$, there is an open neighborhood $V$ of $a$ and polynomials $A,B\in K[Y_0,\ldots,Y_N]$ with
--   $$
--   B(\widehat Y(z))\ne0,\qquad f_{tm}(z)=A(\widehat Y(z))/B(\widehat Y(z))
--   \quad(z\in U\cap V).
--   $$
--   Thus each coefficient is locally a regular rational function of the translation parameter. The neighborhoods and fractions may depend on the coefficient and the point. At every $(x',y')\in U$, the tuple obtained by evaluating $P_t$ at $\widehat X(x')$ and its coefficient functions at $(x',y')$ is nonzero and represents $x'+y'$ in $\mathbf P^N$.
--
--   **Formalization Note.** This is an auxiliary affine-chart version of the quadratic families in the sources, not a verbatim numbered theorem. Coefficient functions are stored in the full function ring; their values outside $U$ are unrestricted. The local fraction condition uses only the second input block, and all open sets carry the induced multiprojective Zariski topology. No common neighborhood or rational expression is required for different coefficients. The degree bound permits inhomogeneous quadratic polynomials; zero-dimensional groups are included.
--
--   **Verified homogeneous-coordinate reduction (8 October 2026).** An accepted proof-sketch constructs simultaneous pivot neighborhoods, pulls parameter-only coefficient functions back to pairs, and proves the homogeneous scaling identities that preserve both coefficient fractions and projective output. The sole remaining input is [homogeneous quadratic translation families](https://prove2.me/theorems/b5c27c68-91c2-40aa-bc97-c75b74f2d340). Their geometric reembedding and existence remain Open; the affine-chart conversion is proved. The original formal statement is unchanged.
-- source:
--   L. Rovelli, Explicit equivariant compactification and Riemann-Roch for algebraic groups, ETH dissertation 14704 (2002), Section 3.3, definition of families described by forms over the affine parameter ring, pp.63–64, Theorem 3.3.2, p.64, and the rational-coefficient paragraph before Corollary 3.3.4, p.66; the existence of a suitable projective embedding is Theorem 3.4.5 and Theorem 3.4.6(2), p.72. https://doi.org/10.3929/ethz-a-004445245 ; https://www.research-collection.ethz.ch/bitstreams/63ac9c62-da67-437e-9dcb-413054fb5550/download . See also H. Lange, Families of translations of commutative algebraic groups, J. Algebra 109(1) (1987), 260–265, DOI 10.1016/0021-8693(87)90174-8. Auxiliary formulation after restriction to the group and normalization on input charts; the first block here is the translated point and the second is the parameter. The regular reembedding, quadratic translation family, and its comparison with this concrete function-ring interface remain Open. Simultaneous local fractions and their exact polynomial degree and evaluation properties are proved in the parent reduction.

import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem exists_quadratic_translation_regular_coefficients
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ c : (projectiveSquare K F.ambientDimension).FactorIndex →
              Fin (F.ambientDimension+1),
          (∀ xy ∈ U, ∀ i : (projectiveSquare K F.ambientDimension).FactorIndex,
            (projectiveSquare K F.ambientDimension).coordinate
              (F.additionPair xy.1 xy.2) ⟨i,c i⟩ ≠ 0) ∧
          ∃ P : Fin (F.ambientDimension+1) →
              MvPolynomial (Fin (F.ambientDimension+1)) ((F.Point × F.Point) → K),
          (∀ t, ∀ m ∈ (P t).support, (∑ j, m j) ≤ 2) ∧
          (∀ t, ∀ m ∈ (P t).support, ∀ xy ∈ U,
            ∃ V : Set (F.Point × F.Point),
              @IsOpen _ (TopologicalSpace.induced (fun zw => F.additionPair zw.1 zw.2)
                (projectiveSquare K F.ambientDimension).zariskiTopology) V ∧ xy ∈ V ∧
              ∃ A B : MvPolynomial (Fin (F.ambientDimension+1)) K,
                ∀ zw ∈ U ∩ V,
                  let w : Fin (F.ambientDimension+1) → K := fun j =>
                    (projectiveSquare K F.ambientDimension).coordinate
                      (F.additionPair zw.1 zw.2) ⟨(1 : Fin 2),j⟩ /
                    (projectiveSquare K F.ambientDimension).coordinate
                      (F.additionPair zw.1 zw.2) ⟨(1 : Fin 2),c (1 : Fin 2)⟩
                  MvPolynomial.eval w B ≠ 0 ∧
                    (P t).coeff m zw = MvPolynomial.eval w A / MvPolynomial.eval w B) ∧
          ∀ xy ∈ U,
            let w : Fin (F.ambientDimension+1) → K := fun j =>
              (projectiveSquare K F.ambientDimension).coordinate
                (F.additionPair xy.1 xy.2) ⟨(0 : Fin 2),j⟩ /
              (projectiveSquare K F.ambientDimension).coordinate
                (F.additionPair xy.1 xy.2) ⟨(0 : Fin 2),c (0 : Fin 2)⟩
            ∃ h : (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point × F.Point => K) xy) w (P t)) ≠ 0,
              Projectivization.mk K (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point × F.Point => K) xy) w (P t)) h =
                  (xy.1+xy.2).val := by sorry

end PhilipponMultiplicity
