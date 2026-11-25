-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_fg_map_of_injective_f02305c255ad
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_fg_map_of_injective_f02305c255ad
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:37:17.867206+00:00
-- url     : https://prove2.me/theorems/25d13298-f961-4542-bc37-50d90399b9f7
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume fg of fg map of injective f02305c255ad: P2 M Ground Theory Heights  Heights Finite Covolume fg of fg map of injective f02305c255ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume fg of fg map of injective f02305c255ad construction uses the P2 M Ground Theory Heights  Heights Finite Covolume fg of fg map of injective f02305c255ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementLattice.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementLattice.lean#L19-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_fg_map_of_injective_f02305c255ad {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {H : AddSubgroup A} (φ : A →+ B) (hφ : Function.Injective φ) (hH : (H.map φ).FG) : H.FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«fg_of_fg_map_of_injective» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_fg_of_fg_map_of_injective_f02305c255ad
