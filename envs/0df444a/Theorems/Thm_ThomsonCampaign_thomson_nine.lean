-- Prove2me | Theorems.Thm_ThomsonCampaign_thomson_nine
-- name    : ThomsonCampaign.thomson_nine
-- status  : Open
-- author  : @vatsj
-- created : 2026-10-13T22:10:33.729356+00:00
-- url     : https://prove2.me/theorems/544abb71-d426-49a4-a00f-d43a7fe10013
-- title:
--   Thomson problem, $N = 9$: a tricapped trigonal prism is optimal
-- statement:
--   There is a parameter $z \in (0,1)$ such that the tricapped trigonal prism with parameter $z$ is a configuration of 9 distinct points on the unit sphere whose Coulomb energy is at most that of every configuration of 9 distinct points on the unit sphere. Competing configurations are arbitrary and uniqueness is not required. Numerically $z \approx 0.70365$ and the energy is $\approx 25.759986531$.
-- source:
--   Numerically best-known minimiser for N = 9; stated as the stretch target thomson_nine in https://github.com/huwngtran/thomson-n7-lean (here with the membership conjunct added).

import Mathlib
import Definitions.Def_ThomsonCampaign_Basic
import Definitions.Def_ThomsonCampaign_Configurations

open Real

namespace ThomsonCampaign
/-- **N = 9.** Some D3h tricapped trigonal prism (numerically `z ≈ 0.70365`, energy `≈ 25.759986531`)
is a global minimiser among 9-point configurations. -/
theorem thomson_nine :
    ∃ z ∈ Set.Ioo (0 : ℝ) 1, triCapPrism z ∈ SphereConfig 9 ∧
      ∀ x ∈ SphereConfig 9, coulombEnergy (triCapPrism z) ≤ coulombEnergy x := by
  sorry
end ThomsonCampaign
