-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_subdiff_subset_dom_eq
-- name    : RockafellarMaxMono.Cyclic.subdiff_subset_dom_eq
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-30T20:43:14.427696+00:00
-- url     : https://prove2.me/theorems/927dcf98-3f80-4fd5-ac0d-b03083ec7724
-- title:
--   Pointwise subdifferential inclusion forces equal domains (infty-bookkeeping for (3.6))
-- statement:
--   Rockafellar, "On the maximal monotonicity of subdifferential mappings", Pacific J. Math. 33 (1970), §3, proof of Theorem B, equation (3.6): infinity bookkeeping. Let E be a real Banach space and let f, g : E -> EReal be lower semicontinuous and proper convex (Shared.ProperConvex). If the subdifferential of f is pointwise contained in the subdifferential of g (Shared.subdiff f x ⊆ Shared.subdiff g x for every x), then f and g take the value +∞ at exactly the same points: f x = +∞ iff g x = +∞. Lower semicontinuity is essential for this step: without it, the pointwise inclusion can hold while the effective domains differ. This is the first decomposition step of the reduction of the lsc case of (3.6) to the finite-continuous core RockafellarMaxMono.Cyclic.finite_subdiff_subset_eq_add_const (whose proof architecture is ACCEPTED), and hence a prerequisite for the assembly proving RockafellarMaxMono.Cyclic.subdiff_subset_eq_add_const.

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff

namespace RockafellarMaxMono.Cyclic

/-- Rockafellar, "On the maximal monotonicity of subdifferential mappings",
    Pacific J. Math. 33 (1970), §3, proof of Theorem B, (3.6):
    ∞-bookkeeping. For lower-semicontinuous proper convex `f g` on a real
    Banach space, a pointwise inclusion of subdifferentials forces `f` and `g`
    to take the value +∞ at exactly the same points. Lower semicontinuity
    is essential: without it the inclusion can hold while the effective domains
    differ. This is the first decomposition step of the reduction of the lsc
    case of (3.6) to the finite-continuous core
    `finite_subdiff_subset_eq_add_const`. -/
theorem subdiff_subset_dom_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f g : E → EReal)
    (hf : Shared.ProperConvex f) (hflsc : LowerSemicontinuous f)
    (hg : Shared.ProperConvex g) (hglsc : LowerSemicontinuous g)
    (hsub : ∀ x : E, Shared.subdiff f x ⊆ Shared.subdiff g x) :
    ∀ x : E, f x = ⊤ ↔ g x = ⊤ := by
  sorry

end RockafellarMaxMono.Cyclic
