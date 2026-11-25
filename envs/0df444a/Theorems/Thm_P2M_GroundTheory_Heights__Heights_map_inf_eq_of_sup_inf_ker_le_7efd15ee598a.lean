-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_inf_eq_of_sup_inf_ker_le_7efd15ee598a
-- name    : P2M_GroundTheory_Heights__Heights_map_inf_eq_of_sup_inf_ker_le_7efd15ee598a
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:48:35.650398+00:00
-- url     : https://prove2.me/theorems/5bb82d28-bf43-5397-86d0-fdb6e2059056
-- title:
--   P2 M Ground Theory Heights  Heights map inf eq of sup inf ker le 7efd15ee598a: P2 M Ground Theory Heights  Heights map inf eq of sup inf ker le 7efd15ee598a
-- statement:
--   The P2 M Ground Theory Heights  Heights map inf eq of sup inf ker le 7efd15ee598a construction uses the P2 M Ground Theory Heights  Heights map inf eq of sup inf ker le 7efd15ee598a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadical.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadical.lean#L13-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadical
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_map_inf_eq_of_sup_inf_ker_le_7efd15ee598a {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) (I J : Ideal R)
    (h : (I ⊔ J) ⊓ RingHom.ker φ ≤ RingHom.ker φ * (I ⊔ J)) :
    (I ⊓ J).map φ = I.map φ ⊓ J.map φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«map_inf_eq_of_sup_inf_ker_le» := P2M_GroundTheory_Heights__Heights_map_inf_eq_of_sup_inf_ker_le_7efd15ee598a
