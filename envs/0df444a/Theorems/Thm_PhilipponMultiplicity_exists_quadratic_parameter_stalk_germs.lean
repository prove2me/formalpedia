-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_quadratic_parameter_stalk_germs
-- name    : PhilipponMultiplicity.exists_quadratic_parameter_stalk_germs
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-09T01:00:30.669295+00:00
-- url     : https://prove2.me/theorems/4a13fb94-dc80-44f0-98bb-678914f578b5
-- title:
--   Quadratic translation germs over parameter stalks
-- statement:
--   Let $K$ be algebraically closed of characteristic zero and let $E$ be a connected commutative algebraic group with a locally closed projective embedding. There is a projective realization $F\subseteq\mathbf P^N$ and an algebraic group isomorphism $E\to F$, regular in both directions, with the following property.
--
--   Every pair $(x,y)\in F\times F$ admits an index $c$ with $Y_c(y)\ne0$. On this parameter chart write $z_j=Y_j/Y_c$, let $I_c$ be the ideal of polynomials vanishing on all its normalized group points, and put
--   $$R_c=K[Z_0,\ldots,Z_N]/I_c,\qquad
--   \mathfrak p_y=\ker(\operatorname{ev}_{z(y)}:R_c\to K).$$
--   There are forms
--   $$P_t\in (R_c)_{\mathfrak p_y}[X_0,\ldots,X_N]\qquad(0\le t\le N)$$
--   homogeneous of degree two in $X$. Choose for each stalk coefficient its fixed localization representative $a/s$, with $s\notin\mathfrak p_y$. Evaluate that coefficient at $y'$ by $a(z(y'))/s(z(y'))$ whenever the pivot is nonzero, with value zero off the pivot chart. Evaluate each form by its finite monomial-support sum, denoting the resulting value by $P_t(X(x');y')$.
--
--   For all $(x',y')$ sufficiently near $(x,y)$ in the actual induced multiprojective Zariski topology, the evaluated tuple is nonzero and
--   $$[P_0(X(x');y'):\cdots:P_N(X(x');y')]=x'+y'.$$
--   The coefficients belong to the parameter stalk at $y$; the assertion does not supply a common principal denominator or a principal neighborhood.
--
--   **Formalization Note.** This is an auxiliary formulation of local quadratic translation data, not a verbatim source theorem. Fraction representatives are the fixed choices in the parameter-stalk definition. Their pointwise evaluation is not asserted to be a ring homomorphism at all points; the displayed polynomial value is explicitly a finite sum. Every chosen denominator is nonzero at $y$. The parent reduction proves that all coefficients spread to one principal chart, that this chart is open in the pair topology, and that degree and projective specialization are preserved. Existence of the reembedding and of these quadratic germs, including comparison with the concrete projective point model, remains Open. Individual zero forms are permitted.
-- source:
--   Auxiliary stalk form of local homogeneous translation families. L. Rovelli, Explicit equivariant compactification and Riemann-Roch for algebraic groups, ETH dissertation 14704 (2002), Section 3.3, pp.63–66, particularly the definition of forms over an affine parameter ring and Theorem 3.3.2; https://doi.org/10.3929/ethz-a-004445245 ; https://www.research-collection.ethz.ch/bitstreams/63ac9c62-da67-437e-9dcb-413054fb5550/download . The coordinate-ring stalk and principal-open interpretation is Stacks Project, Section 26.5, Lemma 26.5.4(3),(6), https://stacks.math.columbia.edu/tag/01HR . This exact point-model and chosen-fraction germ formulation is auxiliary. Its geometric realization is explicitly retained as an Open obligation.

import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_ParameterStalk
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem exists_quadratic_parameter_stalk_germs
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point,
          ∃ (c : Fin (F.ambientDimension + 1)) (hy : y.val.rep c ≠ 0),
          ∃ P : Fin (F.ambientDimension + 1) →
              MvPolynomial (Fin (F.ambientDimension + 1)) (ParameterStalk.Ring F c y hy),
            (∀ t, ∀ m ∈ (P t).support, ∑ j, m j = 2) ∧
            ∀ᶠ xy : F.Point × F.Point in
              @nhds _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
                (projectiveSquare K F.ambientDimension).zariskiTopology) (x,y),
              ∃ h : (fun t => ParameterStalk.formValue F c y hy (P t) xy.1 xy.2) ≠ 0,
                Projectivization.mk K (fun t => ParameterStalk.formValue F c y hy (P t) xy.1 xy.2) h =
                  (xy.1 + xy.2).val := by sorry

end PhilipponMultiplicity
