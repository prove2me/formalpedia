-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isRelevant_finIdeal_iff_f29f08675567
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_isRelevant_finIdeal_iff_f29f08675567
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:55.880872+00:00
-- url     : https://prove2.me/theorems/8c6f0510-cb76-4d01-82c7-9afcca197916
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow is Relevant fin Ideal iff f29f08675567: P2 M Ground Theory Heights  Heights Objects Chow is Relevant fin Ideal iff f29f08675567
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow is Relevant fin Ideal iff f29f08675567 construction uses the P2 M Ground Theory Heights  Heights Objects Chow is Relevant fin Ideal iff f29f08675567 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L69-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_isRelevant_finIdeal_iff_f29f08675567 (W : Ideal (MRing (PBlk n))) :
    IsRelevant (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«isRelevant_finIdeal_iff» := P2M_GroundTheory_Heights__Heights_ObjectsChow_isRelevant_finIdeal_iff_f29f08675567
