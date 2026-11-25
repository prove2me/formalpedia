-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_genOpen___7496082c92fd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_genOpen___7496082c92fd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:55.151804+00:00
-- url     : https://prove2.me/theorems/79c88f9b-c781-4078-ae4d-02facd1ee6cf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Iso gen Open   7496082c92fd: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Iso gen Open   7496
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Iso gen Open   7496082c92fd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model is Iso gen Open   7496082c92fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/SpreadIsoModelIff.lean#L138-L141

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_genOpen___7496082c92fd {a : ℕ} (ha : 0 < a) : IsIso (genOpen X a).ι := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«isIso_genOpen_ι» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_genOpen___7496082c92fd
