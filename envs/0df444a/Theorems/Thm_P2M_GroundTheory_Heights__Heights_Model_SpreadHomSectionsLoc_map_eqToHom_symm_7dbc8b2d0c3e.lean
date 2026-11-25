-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_map_eqToHom_symm_7dbc8b2d0c3e
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_map_eqToHom_symm_7dbc8b2d0c3e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:49.962147+00:00
-- url     : https://prove2.me/theorems/6338b007-0621-4f8a-b766-7f138765da14
-- title:
--   P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc map eq To Hom symm 7dbc8b2d0c3e: P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc map eq To Hom symm 7dbc8b2d0c3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc map eq To Hom symm 7dbc8b2d0c3e construction uses the P2 M Ground Theory Heights  Heights Model Spread Hom Sections Loc map eq To Hom symm 7dbc8b2d0c3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadHomSectionsLoc.lean#L18-L21

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

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_map_eqToHom_symm_7dbc8b2d0c3e (Z : Scheme.{0}) {A B : Z.Opens} (h : A = B) (x : Γ(Z, A)) :
    (Z.presheaf.map (eqToHom h).op).hom ((Z.presheaf.map (eqToHom h.symm).op).hom x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadHomSectionsLoc».«map_eqToHom_symm» := P2M_GroundTheory_Heights__Heights_Model_SpreadHomSectionsLoc_map_eqToHom_symm_7dbc8b2d0c3e
