-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_dvd_sub_aeval_73ee1f5d5857
-- name    : P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_dvd_sub_aeval_73ee1f5d5857
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:48.144862+00:00
-- url     : https://prove2.me/theorems/a558b713-65e7-4d14-a318-40b3126b9069
-- title:
--   P2 M Ground Theory Heights  Heights Chart First Group Dvd dvd sub aeval 73ee1f5d5857: P2 M Ground Theory Heights  Heights Chart First Group Dvd dvd sub aeval 73ee1f5d5857
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart First Group Dvd dvd sub aeval 73ee1f5d5857 construction uses the P2 M Ground Theory Heights  Heights Chart First Group Dvd dvd sub aeval 73ee1f5d5857 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFirstGroupDvd.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFirstGroupDvd.lean#L16-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFirstGroupDvd
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
open GroundTheory.Heights₂.Heights.ChartFirstGroupDvd

theorem P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_dvd_sub_aeval_73ee1f5d5857 {R : Type*} [CommRing R] {n : ℕ} (a : MvPolynomial (Fin n) R)
    (σ : Fin n → MvPolynomial (Fin n) R) (hσ : ∀ m, a ∣ σ m - X m) (P : MvPolynomial (Fin n) R) :
    a ∣ P - aeval σ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFirstGroupDvd».«dvd_sub_aeval» := P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_dvd_sub_aeval_73ee1f5d5857
