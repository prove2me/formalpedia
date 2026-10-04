-- Prove2me | Theorems.Thm_PhilipponMultiplicity_regular_map_has_affine_polynomial_charts
-- name    : PhilipponMultiplicity.regular_map_has_affine_polynomial_charts
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-02T16:08:53.163295+00:00
-- url     : https://prove2.me/theorems/be29b42c-517d-45b3-bab6-f06cab2396d5
-- title:
--   Polynomial affine charts for embedded regular maps
-- statement:
--   Let $K$ be an algebraically closed field. Let $X$ and $Y$ be locally closed subsets of finite products of projective spaces over $K$, equipped with their induced Zariski topologies, and let $f:X\to Y$ be regular. For every $x\in X$, there are open subsets $S\subseteq X$ and $T\subseteq Y$, nonnegative integers $m,n$, ideals
--   $$I\subseteq K[t_1,\ldots,t_m],\qquad J\subseteq K[u_1,\ldots,u_n],$$
--   with $J$ radical, homeomorphisms $a:S\to V(J)$ and $b:T\to V(I)$, and polynomials $P_1,\ldots,P_m\in K[u_1,\ldots,u_n]$ such that
--   $$x\in S,\qquad f(S)\subseteq T,\qquad b(f(z))_i=P_i(a(z))\quad(z\in S,\ 1\le i\le m).$$
--   Here $V(I)\subseteq K^m$ and $V(J)\subseteq K^n$ are the sets of common zeros of the corresponding ideals, with their ordinary Zariski topologies. The topology on each zero set is equivalently induced by sending a point to its evaluation ideal in the polynomial prime spectrum.
--
--   This local chart statement expresses the given regular map by polynomial coordinates between affine algebraic sets. No irreducibility, positive-dimensionality, or characteristic-zero hypothesis is imposed.
--
--   **Formalization Note.** The proof promotes local polynomial-fraction descriptions to global polynomial coordinate formulas on affine zero sets, using the clearing ideal and the Nullstellensatz. The required rational charts and their geometric construction are now proved, completing the polynomial-chart theorem. Every theorem dependency of the accepted reduction is now Proved, and this theorem has zero Open leaves. The final affine construction is [proved here](https://prove2.me/theorems/991f1acf-9ff2-4b25-ac1b-ae896736b322). The original formal statement and hypotheses are unchanged.
-- source:
--   Stacks Project, Lemma 27.13.3, tag 01NG, https://stacks.math.columbia.edu/tag/01NG ; Section 26.5, tag 01HR, https://stacks.math.columbia.edu/tag/01HR ; Lemma 26.6.4, tag 01I1, https://stacks.math.columbia.edu/tag/01I1 ; Theorem 10.34.1, tag 00FV, https://stacks.math.columbia.edu/tag/00FV . Auxiliary consequence for locally closed multiprojective point sets: use standard affine charts and principal open refinements, realize the reduced coordinate algebras as finite-variable polynomial quotients, and lift the coordinate functions of the restricted regular map to polynomials. The comparison with the concrete coordinate predicate and induced topologies is part of the statement, not assumed proved.

import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib
set_option autoImplicit false

namespace PhilipponMultiplicity
universe u

theorem regular_map_has_affine_polynomial_charts
    (K : Type u) [Field K] [IsAlgClosed K]
    (M N : MultiProjectiveSpace K) (X Y : Type u)
    (e : X → M.Point) (j : Y → N.Point) (f : X → Y)
    (he : Function.Injective e) (hj : Function.Injective j)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (hY : @IsLocallyClosed _ N.zariskiTopology (Set.range j))
    (hf : M.IsRegularAlong N e (j ∘ f)) (x : X) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    letI : TopologicalSpace Y := TopologicalSpace.induced j N.zariskiTopology
    ∃ (S : Set X) (T : Set Y), IsOpen S ∧ x ∈ S ∧ IsOpen T ∧
      ∃ hST : Set.MapsTo f S T,
      ∃ (m n : ℕ) (I : Ideal (MvPolynomial (Fin m) K))
        (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
      ∃ (a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance))
        (b : @Homeomorph T (MvPolynomial.zeroLocus K I) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K I => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance))
        (P : Fin m → MvPolynomial (Fin n) K),
        ∀ (z : S) (i : Fin m),
          (b ⟨f z.val, hST z.property⟩).val i = MvPolynomial.aeval (a z).val (P i) := by sorry

end PhilipponMultiplicity
