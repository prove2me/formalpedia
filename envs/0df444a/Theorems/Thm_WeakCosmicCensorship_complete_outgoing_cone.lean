-- Prove2me | Theorems.Thm_WeakCosmicCensorship_complete_outgoing_cone
-- name    : WeakCosmicCensorship.complete_outgoing_cone
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T12:57:01.805186+00:00
-- url     : https://prove2.me/theorems/b35d1987-9a55-42f0-9993-ef97f4501edb
-- title:
--   Christodoulou 1999, p. A26: the complete outgoing cone B₀
-- statement:
--   For **every** asymptotically flat vacuum initial data set (not only small data), there is a radius $R_0>0$ such that the outgoing null boundary $C_0^+=\partial J^+(B_{R_0})$ of the ball $B_{R_0}$ has future-complete null generators: every outgoing null geodesic from $\partial B_{R_0}$ with tangent $n+N$ (future unit normal to the initial surface plus outward unit normal to the sphere) is defined on all of $[0,\infty)$.
--
--   Christodoulou takes this as the starting point of his definition of complete future null infinity; it is a corollary of Minkowski stability applied to the exterior of a large ball, which is close to trivial data. It is the first clause of `HasCompleteFutureNullInfinity`, asserted here for arbitrary data.
--
--   **Formalization Note.** This is exactly the first conjunct of `HasCompleteFutureNullInfinity`, separated as a milestone because it holds for all asymptotically flat data, whereas the full completeness is the conjecture.
-- source:
--   Christodoulou 1999, CQG 16 A23-A35, §1 p. A26 (corollary of the stability of Minkowski spacetime: existence of B₀ with future-complete generators of C₀₊); https://doi.org/10.1088/0264-9381/16/12A/302

import Mathlib
import Definitions.Def_scc_coordinate_framework
import Definitions.Def_wcc_initial_data
import Definitions.Def_wcc_spacetime
import Definitions.Def_wcc_complete_null_infinity
open Set StrongCosmicCensorship

namespace WeakCosmicCensorship
theorem complete_outgoing_cone (h k : Field3) (hd : IsAFInitialData h k)
    (D : Development h k) (hD : IsMaximalDevelopment h k D) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ x : Coords3, ‖x‖ = R₀ → ∃ γ : ℝ → Coords,
      IsNullGeodesicOn D.U D.g (Ici 0) γ ∧ γ 0 = D.ι x ∧
        vel γ 0 = (fun A => devNormal h k D x A + (jac34 D.ι x).mulVec (sphereNormal3 h x) A) := by sorry
end WeakCosmicCensorship
