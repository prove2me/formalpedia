-- Prove2me | Theorems.Thm_ThomsonCampaign_thomson_thirty_two
-- name    : ThomsonCampaign.thomson_thirty_two
-- status  : Open
-- author  : @vatsj
-- created : 2026-10-13T22:11:06.258997+00:00
-- url     : https://prove2.me/theorems/2b451df1-b71d-4cb7-b5fe-e6317f9d99b5
-- title:
--   Thomson problem, $N = 32$ (challenge): icosahedron plus dodecahedron is optimal
-- statement:
--   The 32-point configuration formed by an icosahedron and its dual dodecahedron, scaled to the unit sphere, is a configuration of distinct points whose Coulomb energy ($\approx 412.261274651$) is at most that of every configuration of 32 distinct points on the unit sphere.
--
--   This is the challenge case: the three-point semidefinite bound barely improves on the two-point bound here, so a proof likely needs a new idea.
-- source:
--   Numerically best-known minimiser for N = 32.

import Mathlib
import Definitions.Def_ThomsonCampaign_Basic
import Definitions.Def_ThomsonCampaign_Configurations

open Real

namespace ThomsonCampaign
/-- **N = 32 (challenge).** The icosahedron-plus-dodecahedron configuration (numerically
`E ≈ 412.261274651`) is a global minimiser among 32-point configurations. -/
theorem thomson_thirty_two :
    icoDodeca ∈ SphereConfig 32 ∧ ∀ x ∈ SphereConfig 32, coulombEnergy icoDodeca ≤ coulombEnergy x := by
  sorry
end ThomsonCampaign
