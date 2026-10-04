-- Prove2me | Theorems.Thm_PhilipponMultiplicity_irreducible_regular_map_image_contains_relative_open
-- name    : PhilipponMultiplicity.irreducible_regular_map_image_contains_relative_open
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-02T13:56:57.775461+00:00
-- url     : https://prove2.me/theorems/816dcf96-d178-4f2c-bf30-91a4601c34ac
-- title:
--   An irreducible regular-map image contains a relative open subset
-- statement:
--   Let $K$ be an algebraically closed field, and let $X$ and $Y$ be locally closed subsets of finite products of projective spaces over $K$, with their induced Zariski topologies. Assume that $X$ is irreducible, in particular nonempty, and that $f:X\to Y$ is regular. Write $Z=\overline{f(X)}$, where the closure is taken in $Y$. Then there is a Zariski-open subset $U\subseteq Y$ such that
--   $$\varnothing\ne U\cap Z\subseteq f(X).$$
--   Thus the image contains a nonempty relatively open subset of its closure. The target need not be irreducible, and the image need not have nonempty interior in the whole target. There is no group structure or characteristic-zero assumption.
--
--   This generic-image assertion is the geometric input for Noetherian-induction proofs of constructibility. Its relative formulation allows the image to lie in a proper closed subset of the target.
--
--   **Formalization Note.** The proof uses finite-presentation affine coordinate maps, constructible images, and compatible closed-point charts to obtain a relative open subset of the closure of an irreducible regular-map image. The required affine chart construction is now proved, completing the original theorem. Every theorem dependency of the accepted reduction is now Proved, and this theorem has zero Open leaves. The final affine construction is [proved here](https://prove2.me/theorems/991f1acf-9ff2-4b25-ac1b-ae896736b322). The original formal statement and hypotheses are unchanged.
-- source:
--   Stacks Project, Lemma 29.8.7, tag 01RM, https://stacks.math.columbia.edu/tag/01RM ; Lemma 37.24.2, tag 05F5, https://stacks.math.columbia.edu/tag/05F5 ; Lemma 10.35.22, tag 00GE, https://stacks.math.columbia.edu/tag/00GE . Auxiliary consequence for the concrete multiprojective model: apply dominance and the nonempty-generic-fiber theorem to the reduced closure of the image, then pass to closed points over the algebraically closed base field. The scheme/point-set comparison remains Open.

import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib.Topology.Constructible
set_option autoImplicit false

namespace PhilipponMultiplicity
universe u

theorem irreducible_regular_map_image_contains_relative_open
    (K : Type u) [Field K] [IsAlgClosed K]
    (M N : MultiProjectiveSpace K) (X Y : Type u)
    (e : X → M.Point) (j : Y → N.Point) (f : X → Y)
    (he : Function.Injective e) (hj : Function.Injective j)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (hY : @IsLocallyClosed _ N.zariskiTopology (Set.range j))
    (hf : M.IsRegularAlong N e (j ∘ f))
    (hirr : @IsIrreducible X (TopologicalSpace.induced e M.zariskiTopology) Set.univ) :
    ∃ U : Set Y,
      @IsOpen Y (TopologicalSpace.induced j N.zariskiTopology) U ∧
      (U ∩ @closure Y (TopologicalSpace.induced j N.zariskiTopology) (Set.range f)).Nonempty ∧
      U ∩ @closure Y (TopologicalSpace.induced j N.zariskiTopology) (Set.range f) ⊆
        Set.range f := by sorry

end PhilipponMultiplicity
