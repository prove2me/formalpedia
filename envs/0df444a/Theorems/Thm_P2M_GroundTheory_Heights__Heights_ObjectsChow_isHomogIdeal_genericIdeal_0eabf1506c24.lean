-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogIdeal_genericIdeal_0eabf1506c24
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogIdeal_genericIdeal_0eabf1506c24
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:33.126517+00:00
-- url     : https://prove2.me/theorems/62aeaf83-2b38-4721-943e-2901b3c1960b
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow is Homog Ideal generic Ideal 0eabf1506c24: P2 M Ground Theory Heights  Heights Objects Chow is Homog Ideal generic Ideal 0eabf1506c24
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow is Homog Ideal generic Ideal 0eabf1506c24 construction uses the P2 M Ground Theory Heights  Heights Objects Chow is Homog Ideal generic Ideal 0eabf1506c24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsHomogeneousOfIsMultiHomog.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsHomogeneousOfIsMultiHomog.lean#L43-L58

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
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogIdeal_genericIdeal_0eabf1506c24 {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    IsHomogIdeal (genericIdeal P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«isHomogIdeal_genericIdeal» := P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogIdeal_genericIdeal_0eabf1506c24
