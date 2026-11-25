-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_of_mem_pivotAlgP_39117ec39eaa
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_of_mem_pivotAlgP_39117ec39eaa
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:44:55.509706+00:00
-- url     : https://prove2.me/theorems/2aff2804-37e7-5288-9614-7431635767dd
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists of mem pivot Alg P 39117ec39eaa: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists of mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists of mem pivot Alg P 39117ec39eaa construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists of mem pivot Alg P 39117ec39eaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L85-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
variable (F : Type) [Field F] (n : ℕ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_of_mem_pivotAlgP_39117ec39eaa {y : MvPolynomial (Fin n × Fin n) F} (hy : y ∈ pivotAlgP F n) :
    ∃ z : pivotAlg F n, ((z : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F) = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«exists_of_mem_pivotAlgP» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_of_mem_pivotAlgP_39117ec39eaa
