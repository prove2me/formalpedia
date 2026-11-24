-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a
-- name    : P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:29.795363+00:00
-- url     : https://prove2.me/theorems/7c6fdbf5-a6d2-4273-a043-e77543692d33
-- title:
--   P2 M Ground Theory Heights  Heights eval Cone map d62ae25f8d4a: P2 M Ground Theory Heights  Heights eval Cone map d62ae25f8d4a
-- statement:
--   The P2 M Ground Theory Heights  Heights eval Cone map d62ae25f8d4a construction uses the P2 M Ground Theory Heights  Heights eval Cone map d62ae25f8d4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FiniteSupportHeight.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FiniteSupportHeight.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a {ι : Type} {n : ι → ℕ} {F F' : Type*} [CommRing F] [CommRing F'] (φ : F →+* F')
    (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    evalCone (fun k i ↦ φ (z k i)) f = φ (evalCone z f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«evalCone_map» := P2M_GroundTheory_Heights__Heights_evalCone_map_d62ae25f8d4a
