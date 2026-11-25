-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_sumCp_term_nonneg_37bed98ff91a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_sumCp_term_nonneg_37bed98ff91a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:05.479229+00:00
-- url     : https://prove2.me/theorems/ef988fef-5fbb-437f-b707-90a7b1a7e1ca
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model sum Cp term nonneg 37bed98ff91a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model sum Cp term nonneg 37
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model sum Cp term nonneg 37bed98ff91a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model sum Cp term nonneg 37bed98ff91a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/CpEqPrimeWeight.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/CpEqPrimeWeight.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_CpEqPrimeWeight
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_sumCp_term_nonneg_37bed98ff91a (d : ℤ) {p : ℕ} (hp : p.Prime) :
    0 ≤ (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«sumCp_term_nonneg» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_sumCp_term_nonneg_37bed98ff91a
