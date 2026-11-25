-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_exists_injective_880cc7794019
-- name    : P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_exists_injective_880cc7794019
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:27.616843+00:00
-- url     : https://prove2.me/theorems/1dcb3cbe-7a0b-41f8-b21e-020978e446a5
-- title:
--   P2 M Ground Theory Heights  Heights Chart First Group Dvd exists injective 880cc7794019: P2 M Ground Theory Heights  Heights Chart First Group Dvd exists injective 880cc7794019
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart First Group Dvd exists injective 880cc7794019 construction uses the P2 M Ground Theory Heights  Heights Chart First Group Dvd exists injective 880cc7794019 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFirstGroupDvd.lean#L33-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFirstGroupDvd.lean#L33-L141

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
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_exists_injective_880cc7794019 (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (t : Fin n → F) (e : ℕ)
    (hI : IsProjPrime I) (ht : linForm t ∉ I) :
    ∃ φ : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I)),
      Function.Injective φ ∧
      (∀ g, φ (chartX I t e g) = C (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I) g)) ∧
      ∀ im, φ (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im)) =
        genSubst ((aeval (genPt I) (linForm t))⁻¹ • genPt I)
          (fun m => algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m)) im := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFirstGroupDvd».«exists_injective» := P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_exists_injective_880cc7794019
