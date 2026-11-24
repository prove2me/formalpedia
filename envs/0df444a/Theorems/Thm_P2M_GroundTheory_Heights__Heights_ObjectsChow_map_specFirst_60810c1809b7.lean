-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_map_specFirst_60810c1809b7
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_map_specFirst_60810c1809b7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:48.793348+00:00
-- url     : https://prove2.me/theorems/34b625ca-8feb-42ab-b9ae-75d9ba1a09f5
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow map spec First 60810c1809b7: P2 M Ground Theory Heights  Heights Objects Chow map spec First 60810c1809b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow map spec First 60810c1809b7 construction uses the P2 M Ground Theory Heights  Heights Objects Chow map spec First 60810c1809b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L36-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_map_specFirst_60810c1809b7 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {e : ℕ}
    (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R) :
    map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«map_specFirst» := P2M_GroundTheory_Heights__Heights_ObjectsChow_map_specFirst_60810c1809b7
