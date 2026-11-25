-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_basisHom_app_stdSection_7f67ff63214e
-- name    : P2M_GroundTheory_Heights__Heights_Model_basisHom_app_stdSection_7f67ff63214e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:28.432132+00:00
-- url     : https://prove2.me/theorems/2277e5dd-d106-45e0-a244-99426b67c8cd
-- title:
--   P2 M Ground Theory Heights  Heights Model basis Hom app std Section 7f67ff63214e: P2 M Ground Theory Heights  Heights Model basis Hom app std Section 7f67ff63214e
-- statement:
--   The P2 M Ground Theory Heights  Heights Model basis Hom app std Section 7f67ff63214e construction uses the P2 M Ground Theory Heights  Heights Model basis Hom app std Section 7f67ff63214e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBasisIsoFree.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBasisIsoFree.lean#L26-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBasisIsoFree
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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
variable {Y : Scheme.{u}}

theorem P2M_GroundTheory_Heights__Heights_Model_basisHom_app_stdSection_7f67ff63214e (M : Y.Modules) {n : ℕ} (s : Fin n → Γ(M, ⊤)) (i : Fin n) :
    ((basisHom M s).app ⊤).hom (stdSection Y n i) = s i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«basisHom_app_stdSection» := P2M_GroundTheory_Heights__Heights_Model_basisHom_app_stdSection_7f67ff63214e
