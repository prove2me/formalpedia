-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_squarefree_of_isChowForm_e1bcf340834c
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_squarefree_of_isChowForm_e1bcf340834c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:36.287809+00:00
-- url     : https://prove2.me/theorems/71829d3a-c361-4323-bde6-82c41c27e6e8
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow squarefree of is Chow Form e1bcf340834c: P2 M Ground Theory Heights  Heights Objects Chow squarefree of is Chow Form e1bcf340834c
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow squarefree of is Chow Form e1bcf340834c construction uses the P2 M Ground Theory Heights  Heights Objects Chow squarefree of is Chow Form e1bcf340834c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsHomogeneousOfIsMultiHomog.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsHomogeneousOfIsMultiHomog.lean#L18-L31

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_squarefree_of_isChowForm_e1bcf340834c {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) : Squarefree f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«squarefree_of_isChowForm» := P2M_GroundTheory_Heights__Heights_ObjectsChow_squarefree_of_isChowForm_e1bcf340834c
