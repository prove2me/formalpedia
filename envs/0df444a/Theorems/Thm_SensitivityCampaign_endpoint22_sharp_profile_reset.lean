-- Prove2me | Theorems.Thm_SensitivityCampaign_endpoint22_sharp_profile_reset
-- name    : SensitivityCampaign.endpoint22_sharp_profile_reset
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-24T07:50:55.1544+00:00
-- url     : https://prove2.me/theorems/0228d875-c060-4b50-90ef-80a215cf73b9
-- title:
--   Sharp comparison of the initial and final 22-level profiles
-- statement:
--   Let $P_0$ and $P_4$ be the initial and final sensitivity profiles of the four-stage, 22-level construction on 5,591 vertices. Put $u=3487007904161347435$ and $v=344500417784$. At every profile coordinate $c$,
--   $$
--   vP_4(c)\le uP_0(c).
--   $$
--
--   At flat table index $2284$, equality holds and the initial entry is positive. Thus $u/v$ is the least multiplier for the comparison of these two tables. This comparison is the numerical step in the sharpened four-stage upper bound.
-- source:
--   Original finite certificate by yousofy, Sensitivity213981Formal.Endpoint22NumericData, profileTable0 and profileTable4, flat index 2284. Exact rational comparison computed from the tables underlying https://prove2.me/theorems/e3718744-9a2e-406a-ba8c-5464cad48d6a .

import Definitions.Def_Sensitivity213981Formal_Endpoint22NumericData
open Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22
open Sensitivity213981Formal.ThreeBoundFullProfile
open Sensitivity213981Formal.ThreeBoundNumeric

theorem SensitivityCampaign.endpoint22_sharp_profile_reset : (∀ c : Coord 22, 344500417784 * profile4 c ≤ 3487007904161347435 * profile0 c) ∧
    344500417784 * profileTable4.get 2284 = 3487007904161347435 * profileTable0.get 2284 ∧
    0 < profileTable0.get 2284 := by sorry
