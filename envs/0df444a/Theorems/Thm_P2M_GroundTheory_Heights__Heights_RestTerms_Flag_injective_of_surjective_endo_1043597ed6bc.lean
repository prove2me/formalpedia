-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_injective_of_surjective_endo_1043597ed6bc
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_injective_of_surjective_endo_1043597ed6bc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:53.23717+00:00
-- url     : https://prove2.me/theorems/519b3c32-d4c0-5e16-9825-cc26a77f46d8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag injective of surjective endo 1043597ed6bc: P2 M Ground Theory Heights  Heights Rest Terms Flag injective of surjective endo 1043597ed6bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag injective of surjective endo 1043597ed6bc construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag injective of surjective endo 1043597ed6bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L15-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_injective_of_surjective_endo_1043597ed6bc {R : Type*} [CommRing R] [IsNoetherianRing R]
    (φ : R →+* R) (hφ : Function.Surjective φ) : Function.Injective φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«injective_of_surjective_endo» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_injective_of_surjective_endo_1043597ed6bc
