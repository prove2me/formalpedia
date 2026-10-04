-- Prove2me | Theorems.Thm_PhilipponMultiplicity_regular_map_has_affine_rational_charts
-- name    : PhilipponMultiplicity.regular_map_has_affine_rational_charts
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-02T17:11:10.080421+00:00
-- url     : https://prove2.me/theorems/f8293089-e9f0-494d-9947-16123aeb1751
-- title:
--   Affine charts with local rational formulas for regular maps
-- statement:
--   Let $K$ be an algebraically closed field, and let $X$ and $Y$ be locally closed subsets of finite products of projective spaces over $K$, with their induced Zariski topologies. Let $f:X\to Y$ be regular. For each $x\in X$, there are open subsets $S\subseteq X$ and $T\subseteq Y$, nonnegative integers $m,n$, ideals
--   $$I\subseteq K[t_1,\ldots,t_m],\qquad J\subseteq K[u_1,\ldots,u_n],$$
--   with $J$ radical, and homeomorphisms $a:S\to V(J)$ and $b:T\to V(I)$ such that $x\in S$, $f(S)\subseteq T$, and each target coordinate of the restricted map is locally a quotient of polynomials in the source coordinates.
--
--   Precisely, for every $z\in S$ and $1\le i\le m$, there are an open neighborhood $U\subseteq S$ of $z$ and polynomials $P,Q\in K[u_1,\ldots,u_n]$ such that, for all $w\in U$,
--   $$Q(a(w))\ne0,\qquad b(f(w))_i=\frac{P(a(w))}{Q(a(w))}.$$
--   The affine zero sets carry their ordinary Zariski topologies, equivalently the topologies induced by point evaluation ideals in the corresponding polynomial prime spectra. The neighborhoods and fractions may depend on both $z$ and $i$.
--
--   These charts compare the given multihomogeneous description of regularity with local affine rational-coordinate formulas. No irreducibility, positive-dimensionality, or characteristic-zero assumption is made.
--
--   **Formalization Note.** The proof constructs local polynomial lifts for regular maps by multihomogeneous substitution and proves cancellation of projective scaling factors in balanced fractions. The required affine embedding charts are now proved, completing the local rational-coordinate theorem. Every theorem dependency of the accepted reduction is now Proved, and this theorem has zero Open leaves. The final affine construction is [proved here](https://prove2.me/theorems/991f1acf-9ff2-4b25-ac1b-ae896736b322). The original formal statement and hypotheses are unchanged.
-- source:
--   Stacks Project, Lemma 27.13.3, tag 01NG, https://stacks.math.columbia.edu/tag/01NG ; Lemma 26.5.4(3),(6), tag 01HV, https://stacks.math.columbia.edu/tag/01HV ; Lemma 26.6.4, tag 01I1, https://stacks.math.columbia.edu/tag/01I1 . Auxiliary consequence for locally closed multiprojective point sets: standard affine charts, principal-open refinements, reduced finite-type coordinate presentations, and the local fraction description of regular functions. The concrete chart homeomorphisms and comparison with multihomogeneous coordinate regularity are included in the remaining obligation, not supplied by an assumed scheme interface.

import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib
set_option autoImplicit false

namespace PhilipponMultiplicity
universe u

theorem regular_map_has_affine_rational_charts
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
            inferInstance)),
        ∀ (z : S) (i : Fin m), ∃ U : Set S, IsOpen U ∧ z ∈ U ∧
          ∃ P Q : MvPolynomial (Fin n) K, ∀ w ∈ U,
            MvPolynomial.aeval (a w).val Q ≠ 0 ∧
            (b ⟨f w.val, hST w.property⟩).val i =
              MvPolynomial.aeval (a w).val P / MvPolynomial.aeval (a w).val Q := by sorry

end PhilipponMultiplicity
