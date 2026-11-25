-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_linForm_67474a920261
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_linForm_67474a920261
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:08.655803+00:00
-- url     : https://prove2.me/theorems/cb198f96-932d-448b-9901-8e15d58fa45e
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog lin Form 67474a920261: P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog lin Form 67474a920261
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog lin Form 67474a920261 construction uses the P2 M Ground Theory Heights  Heights Objects Chow is Multi Homog lin Form 67474a920261 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDivSuppHorizontalArithVar.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDivSuppHorizontalArithVar.lean#L15-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivSuppHorizontalArithVar
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp Xc)

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_linForm_67474a920261 {n : ℕ} (u : Fin n → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«isMultiHomog_linForm» := P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_linForm_67474a920261
