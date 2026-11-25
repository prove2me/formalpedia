-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_app_restrict_eq_nsmul_d1c116bc0518
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_app_restrict_eq_nsmul_d1c116bc0518
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:46.78522+00:00
-- url     : https://prove2.me/theorems/8cad641a-d6b8-4e8d-8cd1-0404ee98f325
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists app restrict eq nsmul d1c116bc0518: P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists app restrict eq ns
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists app restrict eq nsmul d1c116bc0518 construction uses the P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc exists app restrict eq nsmul d1c116bc0518 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L23-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadHomSectionsLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.SpreadHomSectionsLoc

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_app_restrict_eq_nsmul_d1c116bc0518 (h₁ : ZLocDenominators.Statement) {X : Scheme.{0}}
    (f : X ⟶ SpecZ) (p : Nat.Primes) (U : X.Opens) (V : (U : Scheme.{0}).Opens) (hV : IsAffineOpen V)
    (b : Γ((baseChangeMap f (ZLoc p) ⁻¹ᵁ U : Scheme.{0}), (baseChangeMap f (ZLoc p) ∣_ U) ⁻¹ᵁ V)) :
    ∃ N : ℕ, 0 < N ∧ ¬ (p : ℕ) ∣ N ∧ ∃ c : Γ((U : Scheme.{0}), V),
      (baseChangeMap f (ZLoc p) ∣_ U).app V c = N • b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadHomSectionsLoc».«exists_app_restrict_eq_nsmul» := P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_exists_app_restrict_eq_nsmul_d1c116bc0518
