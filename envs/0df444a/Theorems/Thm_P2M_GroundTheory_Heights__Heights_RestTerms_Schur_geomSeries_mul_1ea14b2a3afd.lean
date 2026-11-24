-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_geomSeries_mul_1ea14b2a3afd
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_geomSeries_mul_1ea14b2a3afd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:26:55.607799+00:00
-- url     : https://prove2.me/theorems/6ce67dde-9b0d-4546-985f-83ea5fc8ca5c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur geom Series mul 1ea14b2a3afd: P2 M Ground Theory Heights  Heights Rest Terms Schur geom Series mul 1ea14b2a3afd
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur geom Series mul 1ea14b2a3afd construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur geom Series mul 1ea14b2a3afd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L53-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_geomSeries_mul_1ea14b2a3afd (a : R) :
    geomSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«geomSeries_mul» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_geomSeries_mul_1ea14b2a3afd
