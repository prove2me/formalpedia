-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_prod_spec_10b4cbe4f025
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_prod_spec_10b4cbe4f025
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:56.004428+00:00
-- url     : https://prove2.me/theorems/8e844fc2-852d-55f3-8f49-d4167125a28c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Alg Indep prod spec 10b4cbe4f025: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivo
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Alg Indep prod spec 10b4cbe4f025 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Pivot Alg Indep prod spec 10b4cbe4f025 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotAlgIndep.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotAlgIndep.lean#L27-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotAlgIndep
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagPivotAlgIndep
variable (F : Type) [Field F] (n : ℕ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_prod_spec_10b4cbe4f025 (m : ℕ) (hm : m < n) (c : Fin n) (hc : m ≤ (c : ℕ)) :
    (∏ i : Fin m, spec F n (⟨i, by omega⟩, ⟨i, by omega⟩)) * spec F n (⟨m, hm⟩, c) = genFrac F n (⟨m, hm⟩, c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagPivotAlgIndep».«prod_spec» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagPivotAlgIndep_prod_spec_10b4cbe4f025
