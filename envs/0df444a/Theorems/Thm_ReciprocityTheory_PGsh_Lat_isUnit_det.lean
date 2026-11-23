-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Lat_isUnit_det
-- name    : ReciprocityTheory.PGsh.Lat.isUnit_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:19:43.302014+00:00
-- url     : https://prove2.me/theorems/aa0c0a45-fe72-4cd3-8061-4d0e83613dcf
-- title:
--   Lat: is Unit det
-- statement:
--   The Lat construction uses the is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VDetEqOneOfIntegral.lean#L68-L69

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

theorem ReciprocityTheory.PGsh.Lat.isUnit_det (L : Lat v ι) : IsUnit L.B.det := by sorry
