-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_stalkMap_eq_iff_germ_581138d9864c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_stalkMap_eq_iff_germ_581138d9864c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:21.146816+00:00
-- url     : https://prove2.me/theorems/f286a0b5-f59d-496c-ab47-8f56de643742
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model stalk Map eq iff germ 581138d9864c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model stalk Map eq iff g
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model stalk Map eq iff germ 581138d9864c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model stalk Map eq iff germ 581138d9864c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GenericImageEqGermImage.lean#L72-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/GenericImageEqGermImage.lean#L72-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GenericImageEqGermImage
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
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
variable {X : Scheme.{u}}
variable [IrreducibleSpace X]
variable {E E' : X.Modules}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_stalkMap_eq_iff_germ_581138d9864c (ψ : E ≅ E')
    (f : E.presheaf.stalk (genericPoint X) → E'.presheaf.stalk (genericPoint X)) :
    (∀ v, ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
      (Scheme.Modules.Hom.mapPresheaf ψ.hom)).hom v = f v) ↔
    ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
      f (E.presheaf.germ U _ hU s) = E'.presheaf.germ U _ hU (Scheme.Modules.Hom.app ψ.hom U s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«stalkMap_eq_iff_germ» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_stalkMap_eq_iff_germ_581138d9864c
