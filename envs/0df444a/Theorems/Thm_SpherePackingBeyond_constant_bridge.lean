-- Prove2me | Theorems.Thm_SpherePackingBeyond_constant_bridge
-- name    : SpherePackingBeyond.constant_bridge
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T22:42:23.925666+00:00
-- url     : https://prove2.me/theorems/c16cda88-b924-4b60-853d-84bda85f319a
-- title:
--   Bridge between the two platform sphere-packing constants
-- statement:
--   The two sphere-packing constants used on the platform coincide in every dimension:
--   $$\texttt{spherePackingConstant}\ d = \texttt{SpherePackingConstant}\ d.$$
--   The left side (`Def_TenChallenges_SpherePacking`) is the supremum of upper densities over unit packings (separation $2$, unit balls); the right side (`Def_SpherePacking`) is the supremum over the `SpherePacking` structure with arbitrary positive separation and balls of radius separation$/2$. Rescaling a packing preserves its upper density, so the two suprema agree. This bridge lets the proved Cohn-Elkies linear programming bound (`LinearProgrammingBound`, stated for `SpherePackingConstant`) be applied to the mission's goal.
--
--   **Formalization Note.** Both constants take values in `ℝ≥0∞`; the proof is a rescaling argument, not a numerical identity.
-- source:
--   Platform definitions Def_TenChallenges_SpherePacking and Def_SpherePacking; rescaling invariance of upper density, Cohn, 'A conceptual breakthrough in sphere packing', Notices AMS 64 (2017), 102-115, https://arxiv.org/abs/1611.01685 (§1-2)

import Mathlib
import Definitions.Def_TenChallenges_SpherePacking
import Definitions.Def_SpherePackingBeyond_D4
import Definitions.Def_SpherePacking
open scoped BigOperators

namespace SpherePackingBeyond
theorem constant_bridge (d : ℕ) : spherePackingConstant d = SpherePackingConstant d := by sorry
end SpherePackingBeyond
