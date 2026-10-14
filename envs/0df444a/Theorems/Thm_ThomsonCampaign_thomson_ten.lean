-- Prove2me | Theorems.Thm_ThomsonCampaign_thomson_ten
-- name    : ThomsonCampaign.thomson_ten
-- status  : Open
-- author  : @vatsj
-- created : 2026-10-13T22:09:54.643104+00:00
-- url     : https://prove2.me/theorems/72455dd8-a8e5-4f86-bc00-0798f0d98cca
-- title:
--   Thomson problem, $N = 10$: a capped square antiprism is optimal
-- statement:
--   There is a parameter $h \in (0,1)$ such that the capped square antiprism with parameter $h$ is a configuration of 10 distinct points on the unit sphere whose Coulomb energy is at most that of every configuration of 10 distinct points on the unit sphere:
--   $$\exists\, h \in (0,1):\quad E(A_h) \le E(x) \ \text{ for all } x.$$
--   Competing configurations are arbitrary; no symmetry is assumed. Uniqueness is not required. The optimal parameter is known only numerically ($h \approx 0.42269$, energy $\approx 32.716949460$), which is why it is existentially quantified.
-- source:
--   Numerically best-known minimiser for N = 10.

import Mathlib
import Definitions.Def_ThomsonCampaign_Basic
import Definitions.Def_ThomsonCampaign_Configurations

open Real

namespace ThomsonCampaign
/-- **N = 10.** Some D4d capped square antiprism (numerically `h ≈ 0.42269`, energy `≈ 32.716949460`)
is a global minimiser among 10-point configurations. -/
theorem thomson_ten :
    ∃ h ∈ Set.Ioo (0 : ℝ) 1, cappedSquareAntiprism h ∈ SphereConfig 10 ∧
      ∀ x ∈ SphereConfig 10, coulombEnergy (cappedSquareAntiprism h) ≤ coulombEnergy x := by
  sorry
end ThomsonCampaign
