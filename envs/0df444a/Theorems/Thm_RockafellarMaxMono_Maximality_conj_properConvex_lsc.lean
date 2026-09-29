-- Prove2me | Theorems.Thm_RockafellarMaxMono_Maximality_conj_properConvex_lsc
-- name    : RockafellarMaxMono.Maximality.conj_properConvex_lsc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:02:25.491155+00:00
-- url     : https://prove2.me/theorems/6a06d827-a26b-4aba-bc1a-0db4754a3926
-- title:
--   §2, p. 210 — the conjugate $f^*$ is a weak* lsc proper convex function on $E^*$
-- statement:
--   Let $E$ be a real Banach space with dual $E^*$, and let $f$ be a lower semicontinuous proper convex function on $E$. Then its conjugate $f^*$ is
--
--   1. lower semicontinuous for the weak* topology on $E^*$,
--   2. lower semicontinuous for the strong (norm) topology on $E^*$, and
--   3. a proper convex function on $E^*$.
--
--   This is what allows the results stated for $f$ (for instance (2.2)) to be applied to $f^*$ on the Banach space $E^*$.
--
--   **Formalization Note** Weak* lower semicontinuity is stated for $f^*$ viewed as a function on Mathlib's `WeakDual ℝ E` (the dual with the weak* topology), via the identity map `StrongDual.toWeakDual`. The paper says "(and hence strongly lower semicontinuous)"; both lower semicontinuity claims are part of the statement.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 210, §2

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Conj

namespace RockafellarMaxMono.Maximality

theorem conj_properConvex_lsc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous (fun w : WeakDual ℝ E => Shared.conj f (StrongDual.toWeakDual.symm w)) ∧
      LowerSemicontinuous (Shared.conj f) ∧ Shared.ProperConvex (Shared.conj f) := by sorry

end RockafellarMaxMono.Maximality
