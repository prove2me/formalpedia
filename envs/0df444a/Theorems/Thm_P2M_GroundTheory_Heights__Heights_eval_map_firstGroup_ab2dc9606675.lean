-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_map_firstGroup_ab2dc9606675
-- name    : P2M_GroundTheory_Heights__Heights_eval_map_firstGroup_ab2dc9606675
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:21.298215+00:00
-- url     : https://prove2.me/theorems/54e6bdf7-b290-4b2b-b5dc-7a99b62716bc
-- title:
--   P2 M Ground Theory Heights  Heights eval map first Group ab2dc9606675: P2 M Ground Theory Heights  Heights eval map first Group ab2dc9606675
-- statement:
--   The P2 M Ground Theory Heights  Heights eval map first Group ab2dc9606675 construction uses the P2 M Ground Theory Heights  Heights eval map first Group ab2dc9606675 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L108-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L108-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_eval_map_firstGroup_ab2dc9606675 {F : Type} [Field F] {n e : ℕ} (p : Ideal (MvPolynomial (Fin e × Fin n) F))
    [p.IsPrime] (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F) :
    eval (fun m => algebraMap F (Localization.AtPrime p) (u m))
        (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f)) =
      algebraMap _ (Localization.AtPrime p) (specFirst f u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_map_firstGroup» := P2M_GroundTheory_Heights__Heights_eval_map_firstGroup_ab2dc9606675
