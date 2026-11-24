-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultihomog_map_iff_cd1cd76dd983
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultihomog_map_iff_cd1cd76dd983
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:56.059696+00:00
-- url     : https://prove2.me/theorems/0e8ed5e2-6d3f-411d-bef6-fac359cebab6
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow is Multihomog map iff cd1cd76dd983: P2 M Ground Theory Heights  Heights Objects Chow is Multihomog map iff cd1cd76dd983
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow is Multihomog map iff cd1cd76dd983 construction uses the P2 M Ground Theory Heights  Heights Objects Chow is Multihomog map iff cd1cd76dd983 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean#L58-L61

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultihomog_map_iff_cd1cd76dd983 {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) {e δ : ℕ} (f : MvPolynomial (Fin (e + 1) × Fin n) R) :
    IsMultihomog (map φ f) δ ↔ IsMultihomog f δ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«isMultihomog_map_iff» := P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultihomog_map_iff_cd1cd76dd983
