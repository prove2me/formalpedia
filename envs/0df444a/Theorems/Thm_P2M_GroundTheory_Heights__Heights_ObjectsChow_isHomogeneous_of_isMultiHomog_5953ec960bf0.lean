-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogeneous_of_isMultiHomog_5953ec960bf0
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogeneous_of_isMultiHomog_5953ec960bf0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:32.22245+00:00
-- url     : https://prove2.me/theorems/3982839d-21d5-4c90-b316-f8d2dbea6f46
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow is Homogeneous of is Multi Homog 5953ec960bf0: P2 M Ground Theory Heights  Heights Objects Chow is Homogeneous of is Multi Homog 5953ec960bf0
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow is Homogeneous of is Multi Homog 5953ec960bf0 construction uses the P2 M Ground Theory Heights  Heights Objects Chow is Homogeneous of is Multi Homog 5953ec960bf0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsHomogeneousOfIsMultiHomog.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsHomogeneousOfIsMultiHomog.lean#L33-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsHomogeneousOfIsMultiHomog
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogeneous_of_isMultiHomog_5953ec960bf0 {n : ℕ} {s : MRing (PBlk n)} {a : Unit → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : s.IsHomogeneous (a ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«isHomogeneous_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogeneous_of_isMultiHomog_5953ec960bf0
