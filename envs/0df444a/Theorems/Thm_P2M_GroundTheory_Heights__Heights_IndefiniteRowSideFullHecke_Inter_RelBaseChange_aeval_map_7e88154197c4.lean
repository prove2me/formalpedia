-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_RelBaseChange_aeval_map_7e88154197c4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_RelBaseChange_aeval_map_7e88154197c4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:06.776336+00:00
-- url     : https://prove2.me/theorems/5f9597b3-83d9-4112-946a-0065a3928301
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Rel Base Change aeval map 7e88154197c4: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Rel Base Chang
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Rel Base Change aeval map 7e88154197c4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Rel Base Change aeval map 7e88154197c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRelBaseChange.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRelBaseChange.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RelBaseChangeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRelBaseChange
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
open MvPolynomial TensorProduct

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_RelBaseChange_aeval_map_7e88154197c4 {F F' : Type} [Field F] [Field F'] [Algebra F F'] {σ τ : Type}
    (g : σ → MvPolynomial τ F) (p : MvPolynomial σ F) :
    aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (MvPolynomial.map (algebraMap F F') p) =
      MvPolynomial.map (algebraMap F F') (aeval g p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«RelBaseChange».«aeval_map» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_RelBaseChange_aeval_map_7e88154197c4
