-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_to_sub_443c20a1e1ad
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_to_sub_443c20a1e1ad
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:59:55.502349+00:00
-- url     : https://prove2.me/theorems/2fb5c143-2334-5b90-840d-fa3dd183a536
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model exists to sub 443c20a1e1ad: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model exists to sub 443c20a1e1ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model exists to sub 443c20a1e1ad construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model exists to sub 443c20a1e1ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L173-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L173-L182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
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
open CategoryTheory AlgebraicGeometry
variable (X : Scheme.{0})

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_to_sub_443c20a1e1ad (a m' : ℕ) :
    ∃ w' : (invOpen X (a * m')).toScheme ⟶ (subOpen X a m').toScheme,
      w' ≫ (subOpen X a m').ι = X.homOfLE (invOpen_le X a m') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«exists_to_sub» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_to_sub_443c20a1e1ad
