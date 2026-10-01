-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_subdiff_cyclically_monotone
-- name    : RockafellarMaxMono.Cyclic.subdiff_cyclically_monotone
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-30T20:35:57.438934+00:00
-- url     : https://prove2.me/theorems/b3bc958f-395f-4aa2-aeea-3cbcccd7d63b
-- title:
--   Subdifferential of an lsc proper convex function is cyclically monotone
-- statement:
--   Rockafellar, "On the maximal monotonicity of subdifferential mappings", Pacific J. Math. 33 (1970), Theorem B, part (1) forward, elementary half. If E is a real Banach space and f : E -> EReal is lower semicontinuous and proper convex (Shared.ProperConvex), then the multivalued map x |-> Shared.subdiff f x is cyclically monotone (in the bundle's IsCyclicallyMonotone sense): summing the subgradient inequalities around any finite cycle of points telescopes to the cyclic-monotonicity inequality. This is a rank-2 standalone lemma of the target node RockafellarMaxMono.Cyclic.maximal_cyclically_monotone_iff_subdiff; it does not unlock the target because the maximality half (no cyclically monotone proper extension exists) needs the Asplund/resolvent density machinery that is not in Mathlib.

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Cyclic_CyclicallyMonotone

namespace RockafellarMaxMono.Cyclic

/-- Rockafellar, "On the maximal monotonicity of subdifferential mappings",
    Pacific J. Math. 33 (1970), Theorem B, part (1) forward, elementary half:
    the subdifferential of a lower-semicontinuous proper convex function on a
    real Banach space is cyclically monotone. Summing the subgradient
    inequalities around any finite cycle of points telescopes to the cyclic
    monotonicity inequality. The maximality half (no cyclically monotone
    proper extension exists) is the deep Asplund/resolvent step and is not
    claimed here. -/
theorem subdiff_cyclically_monotone {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (hsc : LowerSemicontinuous f) :
    IsCyclicallyMonotone (fun x => Shared.subdiff f x) := by
  sorry

end RockafellarMaxMono.Cyclic
