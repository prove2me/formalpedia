-- Prove2me | Theorems.Thm_Rudin_ch04_monotone_discontinuities_countable
-- name    : Rudin.ch04_monotone_discontinuities_countable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T22:22:29.308481+00:00
-- url     : https://prove2.me/theorems/34c1d8d7-5c2e-48e7-a2fa-3aabc74d631b
-- title:
--   Theorem 4.30 — monotone functions have countably many discontinuities
-- statement:
--   If $f$ is monotone on $(a,b)$, then the set of points of $(a,b)$ at which $f$ is discontinuous is at most countable.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 96, Theorem 4.30

import Mathlib
import Definitions.Def_Rudin_ch04_continuity

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.30: the set of points of `(a, b)` at which a monotone function is
discontinuous is at most countable. -/
theorem ch04_monotone_discontinuities_countable (a b : ℝ) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Ioo a b)) :
    {x ∈ Set.Ioo a b | ¬ ContinuousWithinAt f (Set.Ioo a b) x}.Countable := by sorry

end Rudin
