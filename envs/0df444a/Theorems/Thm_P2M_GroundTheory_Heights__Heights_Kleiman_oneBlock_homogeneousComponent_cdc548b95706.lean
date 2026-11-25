-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_oneBlock_homogeneousComponent_cdc548b95706
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_oneBlock_homogeneousComponent_cdc548b95706
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:10:21.118862+00:00
-- url     : https://prove2.me/theorems/a22c1c0a-e90d-57d8-ad42-99dca22987cf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman one Block homogeneous Component cdc548b95706: P2 M Ground Theory Heights  Heights Kleiman one Block homogeneous Component cdc548b95706
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman one Block homogeneous Component cdc548b95706 construction uses the P2 M Ground Theory Heights  Heights Kleiman one Block homogeneous Component cdc548b95706 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointDegreePos.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointDegreePos.lean#L20-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PointDegreePosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPointDegreePos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_oneBlock_homogeneousComponent_cdc548b95706 (f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    oneBlock (S := k) (N := N) (homogeneousComponent n f) =
      homogeneousComponent n (oneBlock (S := k) (N := N) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«oneBlock_homogeneousComponent» := P2M_GroundTheory_Heights__Heights_Kleiman_oneBlock_homogeneousComponent_cdc548b95706
