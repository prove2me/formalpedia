-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_iInf_dc81a4ab244c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_iInf_dc81a4ab244c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:22:53.543821+00:00
-- url     : https://prove2.me/theorems/f9b08403-3925-41d6-b1a5-ed3a5a37042d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Height One Intersection coe i Inf dc81a4ab244c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Height
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Height One Intersection coe i Inf dc81a4ab244c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Height One Intersection coe i Inf dc81a4ab244c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/EquivAt.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/EquivAt.lean#L18-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_EquivAt
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
variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_iInf_dc81a4ab244c :
    ((⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        GroundTheory.Heights₂.Heights.Model.localizedIn p.asIdeal
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K)) : Submodule A K) : Set K) =
      ⋂ (p : Ideal A) (_ : p.IsPrime) (_ : p.height = 1), locIn A K p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«HeightOneIntersection».«coe_iInf» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_iInf_dc81a4ab244c
