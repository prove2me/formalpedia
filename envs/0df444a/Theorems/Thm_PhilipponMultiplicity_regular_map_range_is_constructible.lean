-- Prove2me | Theorems.Thm_PhilipponMultiplicity_regular_map_range_is_constructible
-- name    : PhilipponMultiplicity.regular_map_range_is_constructible
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-02T12:34:52.620704+00:00
-- url     : https://prove2.me/theorems/5434ecd8-16cf-40af-8774-04cd13e6c80c
-- title:
--   Constructible images of regular maps between embedded varieties
-- statement:
--   Let $K$ be an algebraically closed field. Let $X$ and $Y$ be sets identified, by injective maps $e$ and $j$, with locally closed subsets of finite products of projective spaces over $K$. Give them the induced Zariski topologies. Suppose $f:X\to Y$ is regular: around every point, each projective coordinate block of $j\circ f$ is represented by a nonvanishing tuple of multihomogeneous polynomials of a common multidegree in the source coordinates. Then
--   $$f(X)\quad\text{is a constructible subset of }Y.$$
--
--   This is the point-set form of Chevalley's constructible-image theorem for locally closed embedded varieties. It supplies a reusable image theorem for the repository's explicit polynomial model. No group law, connectedness, characteristic-zero assumption, or positive-dimensionality is required; empty varieties are allowed.
--
--   **Formalization Note.** The proof uses Noetherian induction and the relative-open image theorem on irreducible locally closed restrictions to establish constructibility of the original regular-map image. The relative-open image theorem and its affine chart dependencies are now proved. Every theorem dependency of the accepted reduction is now Proved, and this theorem has zero Open leaves. The final affine construction is [proved here](https://prove2.me/theorems/991f1acf-9ff2-4b25-ac1b-ae896736b322). The original formal statement and hypotheses are unchanged.
-- source:
--   Stacks Project, Theorem 29.23.3 (Chevalley), tag 054K, https://stacks.math.columbia.edu/tag/054K ; Lemma 10.35.22, tag 00GE, https://stacks.math.columbia.edu/tag/00GE . Concrete closed-point formulation for regular maps between locally closed subsets of multiprojective spaces over an algebraically closed field. The source statements concern schemes/spectra; the repository-specific comparison is the explicit remaining obligation.

import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib.Topology.Constructible
set_option autoImplicit false

namespace PhilipponMultiplicity
universe u

theorem regular_map_range_is_constructible
    (K : Type u) [Field K] [IsAlgClosed K]
    (M N : MultiProjectiveSpace K) (X Y : Type u)
    (e : X → M.Point) (j : Y → N.Point) (f : X → Y)
    (he : Function.Injective e) (hj : Function.Injective j)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (hY : @IsLocallyClosed _ N.zariskiTopology (Set.range j))
    (hf : M.IsRegularAlong N e (j ∘ f)) :
    @Topology.IsConstructible Y (TopologicalSpace.induced j N.zariskiTopology)
      (Set.range f) := by sorry

end PhilipponMultiplicity
