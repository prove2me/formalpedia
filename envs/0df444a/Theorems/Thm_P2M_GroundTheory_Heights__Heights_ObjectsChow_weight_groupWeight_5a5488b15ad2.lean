-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_weight_groupWeight_5a5488b15ad2
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_weight_groupWeight_5a5488b15ad2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:01.359806+00:00
-- url     : https://prove2.me/theorems/bb2350a1-182d-4288-8d52-73e006a511eb
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow weight group Weight 5a5488b15ad2: P2 M Ground Theory Heights  Heights Objects Chow weight group Weight 5a5488b15ad2
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow weight group Weight 5a5488b15ad2 construction uses the P2 M Ground Theory Heights  Heights Objects Chow weight group Weight 5a5488b15ad2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L46-L51

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_weight_groupWeight_5a5488b15ad2 {k : ℕ} (m : Fin k × Fin n →₀ ℕ) :
    Finsupp.weight (groupWeight k n) m = fun i => ∑ j, m (i, j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«weight_groupWeight» := P2M_GroundTheory_Heights__Heights_ObjectsChow_weight_groupWeight_5a5488b15ad2
