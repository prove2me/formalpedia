-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Lat_pts_subset_iff
-- name    : ReciprocityTheory.PGsh.Lat.pts_subset_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:35.606487+00:00
-- url     : https://prove2.me/theorems/b06580e2-049b-4f8e-b4ab-f3cdab04e9bd
-- title:
--   Lat: pts subset iff
-- statement:
--   The Lat construction uses the pts subset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L71-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L71-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_NearIdentityColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open Matrix
open ReciprocityTheory.PGsh.Lat
variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.PGsh.Lat.pts_subset_iff (L' L : Lat v ι) :
    L'.pts ⊆ L.pts ↔ IsIntegralMat v (L.B⁻¹ * L'.B) := by sorry
