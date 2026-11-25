-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BundlesAgree_hyps_122944737f56
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BundlesAgree_hyps_122944737f56
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:12.978976+00:00
-- url     : https://prove2.me/theorems/d552b7bd-b057-588a-93bc-7fdaf50b3dbe
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Bundles Agree hyps 122944737f56: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Bundles Agree hyps 12
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Bundles Agree hyps 122944737f56 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Bundles Agree hyps 122944737f56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L520-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean#L520-L527

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BundlesAgree_hyps_122944737f56 :
    IsIntegral specInt ∧ IsNormalScheme specInt ∧ IsLocallyNoetherian specInt ∧
    IsVectorBundle (𝟙_ specInt.Modules) ∧
    ∀ x : specInt, ringKrullDim (specInt.presheaf.stalk x) = 1 →
      (GenericStalkIso.refl (𝟙_ specInt.Modules)).toAddEquiv '' germImage (𝟙_ specInt.Modules) x =
        germImage (𝟙_ specInt.Modules) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«BundlesAgree».«hyps» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BundlesAgree_hyps_122944737f56
