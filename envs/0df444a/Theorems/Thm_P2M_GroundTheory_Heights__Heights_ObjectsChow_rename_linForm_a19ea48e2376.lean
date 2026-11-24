-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_rename_linForm_a19ea48e2376
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_rename_linForm_a19ea48e2376
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:19.767551+00:00
-- url     : https://prove2.me/theorems/3cb5f380-2cae-4fc2-9715-fcc913322a9c
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow rename lin Form a19ea48e2376: P2 M Ground Theory Heights  Heights Objects Chow rename lin Form a19ea48e2376
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow rename lin Form a19ea48e2376 construction uses the P2 M Ground Theory Heights  Heights Objects Chow rename lin Form a19ea48e2376 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L22-L24

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_rename_linForm_a19ea48e2376 (u : Fin n → ℤ) :
    rename (blk n) (linForm u) = IndefiniteRowSideFullHecke.ArithBezout.linForm u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«rename_linForm» := P2M_GroundTheory_Heights__Heights_ObjectsChow_rename_linForm_a19ea48e2376
