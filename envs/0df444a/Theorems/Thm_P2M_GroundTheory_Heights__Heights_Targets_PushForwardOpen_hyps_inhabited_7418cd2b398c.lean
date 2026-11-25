-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_hyps_inhabited_7418cd2b398c
-- name    : P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_hyps_inhabited_7418cd2b398c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:53:13.728895+00:00
-- url     : https://prove2.me/theorems/63712464-6504-577c-965c-923e761b2bc5
-- title:
--   P2 M Ground Theory Heights  Heights Targets Push Forward Open hyps inhabited 7418cd2b398c: P2 M Ground Theory Heights  Heights Targets Push Forward Open hyps inhabited 7418cd2b398c
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Push Forward Open hyps inhabited 7418cd2b398c construction uses the P2 M Ground Theory Heights  Heights Targets Push Forward Open hyps inhabited 7418cd2b398c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L33-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L33-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_KerEqBotOfCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsPushForwardOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_DivPushResSideInhabitants
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_hyps_inhabited_7418cd2b398c :
    (∀ i : Fin 1, IsPotential p1 ((fun _ : Fin 1 => fsPot) i)) ∧
    IsOpen PushForwardOpen.finitePlane ∧
    (∀ x ∈ PushForwardOpen.finitePlane, ∀ j, x ∈ (p1.chart j).source →
      AnalyticAt ℂ (PushForwardOpen.projLineAffineCoordinate ∘ (p1.chart j).symm) (p1.chart j x) ∧
        LinearMap.det (fderiv ℂ (PushForwardOpen.projLineAffineCoordinate ∘ (p1.chart j).symm) (p1.chart j x) :
          (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) ≠ 0) ∧
    (∀ j, ∀ᵐ u, u ∈ (p1.chart j).target → (p1.chart j).symm u ∉ PushForwardOpen.finitePlane →
      locDens p1 (fun _ : Fin 1 => fsPot) j u = 0) ∧
    (∀ᵐ y, (PushForwardOpen.projLineAffineCoordinate ⁻¹' {y} ∩ PushForwardOpen.finitePlane).Finite) ∧
    MIntegrable p1 (fun _ : Fin 1 => fsPot) (fun _ => (1 : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«PushForwardOpen».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_hyps_inhabited_7418cd2b398c
