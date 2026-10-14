-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_born_component_subset
-- name    : PersistClust.Count.theorem_4_5_born_component_subset
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T17:17:21.335015+00:00
-- url     : https://prove2.me/theorems/abce3a62-558d-44ba-9ffe-e454ea016029
-- title:
--   Theorem 4.5 support - born components live inside the c*delta-superlevel component
-- statement:
--   Let f be a real-valued function on a metric space X. If t > c*delta and the points x0 and y are joined inside the t-superlevel set of f (they lie in the same path-connected component of the superlevel set at level t), then y belongs to the path-connected component of x0 inside the (c*delta)-superlevel set of f. This is the containment step of the elder chase: superlevel sets are antitone (level t members are members at every level below t), so the joined-in relation is preserved when descending from level t to the lower level c*delta. The proof instantiates the filtration-law structure on the superlevel filtration and applies its antitone field together with joined-in monotonicity.
-- source:
--   The born-component containment step of the L_tau cluster in the proof of Theorem 4.5, Persistence-Based Clustering in Riemannian Manifolds (rr/6968). Child of theorem_4_5 (id 8476e8c8-3232-437b-939f-4ea37c366d80); companion of the accepted theorem_4_5_elder_chase_essential_bar (id 9cfba490-b1d0-4057-9d74-80806c1fc1df), theorem_4_5_essential_birth_gt_bound (id 652b6c32-8688-424f-a910-1dda7f9c2b6d) and theorem_4_5_separated_bar_death_lower_bound (id 819f90bb-5169-40a5-a199-f0dc04aa2120). The inlined superlevel filtration-law instance is the same fact as in the auxiliary layer of the accepted solutions lineage (theorem_4_5_interleaving_corrected / theorem_4_8_core).

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_FiltrationLaw

open PersistClust.Count

namespace PersistClust.Count

theorem theorem_4_5_born_component_subset {X : Type*} [MetricSpace X] {f : X → ℝ} {c δ t : ℝ} (ht : c * δ < t) {x₀ y : X}
    (hy : JoinedIn (superlevel f t) x₀ y) :
    y ∈ pathComponentIn (superlevel f (c * δ)) x₀
    := by sorry
