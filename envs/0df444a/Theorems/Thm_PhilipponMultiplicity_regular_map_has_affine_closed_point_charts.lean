-- Prove2me | Theorems.Thm_PhilipponMultiplicity_regular_map_has_affine_closed_point_charts
-- name    : PhilipponMultiplicity.regular_map_has_affine_closed_point_charts
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-02T15:05:52.075616+00:00
-- url     : https://prove2.me/theorems/9a64367d-e7bb-42f3-bf05-e6f195355809
-- title:
--   Compatible affine closed-point charts for regular maps
-- statement:
--   Let $K$ be an algebraically closed field. Let $X$ and $Y$ be locally closed subsets of finite products of projective spaces over $K$, with their induced Zariski topologies, and let $f:X\to Y$ be regular. For every $x\in X$, there are open subsets $S\subseteq X$ and $T\subseteq Y$, finitely generated $K$-algebras
--   $$A=K[t_1,\ldots,t_m]/I,\qquad B=K[u_1,\ldots,u_n]/J,$$
--   homeomorphisms $a:S\to\operatorname{MaxSpec}(B)$ and $b:T\to\operatorname{MaxSpec}(A)$, and a $K$-algebra map $\varphi:A\to B$, such that
--   $$x\in S,\qquad f(S)\subseteq T,\qquad b(f(z))=\varphi^{-1}(a(z))\quad(z\in S).$$
--   Here $m,n$ are nonnegative integers, $I,J$ are ideals, and the maximal spectra have their Zariski topologies. The last equality is an equality of ideals of $A$. No irreducibility or positive-dimensionality is required.
--
--   **Formalization Note.** The proof identifies affine polynomial zero sets with the maximal spectra of their coordinate quotients and checks compatibility of polynomial coordinate maps with the induced quotient homomorphisms. The required polynomial charts are now proved, completing the closed-point chart theorem. Every theorem dependency of the accepted reduction is now Proved, and this theorem has zero Open leaves. The final affine construction is [proved here](https://prove2.me/theorems/991f1acf-9ff2-4b25-ac1b-ae896736b322). The original formal statement and hypotheses are unchanged.
-- source:
--   Stacks Project, Lemma 27.13.3, tag 01NG, https://stacks.math.columbia.edu/tag/01NG ; Lemma 26.6.4, tag 01I1, https://stacks.math.columbia.edu/tag/01I1 ; Lemma 29.22.2, tag 01TQ, https://stacks.math.columbia.edu/tag/01TQ ; Lemma 33.14.1, tag 0478, https://stacks.math.columbia.edu/tag/0478 . Auxiliary consequence for locally closed multiprojective point sets over an algebraically closed field: standard affine charts and affine morphisms, with closed points identified by the Nullstellensatz. The concrete polynomial-model comparison is the remaining obligation.

import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib
set_option autoImplicit false

namespace PhilipponMultiplicity
universe u

theorem regular_map_has_affine_closed_point_charts
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
        (J : Ideal (MvPolynomial (Fin n) K))
        (a : S ≃ₜ MaximalSpectrum (MvPolynomial (Fin n) K ⧸ J))
        (b : T ≃ₜ MaximalSpectrum (MvPolynomial (Fin m) K ⧸ I))
        (φ : (MvPolynomial (Fin m) K ⧸ I) →ₐ[K] (MvPolynomial (Fin n) K ⧸ J)),
        ∀ z : S, (b ⟨f z.val, hST z.property⟩).asIdeal =
          Ideal.comap φ.toRingHom (a z).asIdeal := by sorry

end PhilipponMultiplicity
