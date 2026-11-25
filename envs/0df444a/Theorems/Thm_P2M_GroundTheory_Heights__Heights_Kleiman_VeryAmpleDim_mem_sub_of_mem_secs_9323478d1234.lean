-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_sub_of_mem_secs_9323478d1234
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_sub_of_mem_secs_9323478d1234
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:45.900241+00:00
-- url     : https://prove2.me/theorems/1fba42cf-63df-45fe-9ff1-7d682add694f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim mem sub of mem secs 9323478d1234: P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim mem sub of mem secs 9323478d1234
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim mem sub of mem secs 9323478d1234 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim mem sub of mem secs 9323478d1234 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AmpleAffineGen
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_sub_of_mem_secs_9323478d1234 {H : SubSystem k x Ω} {s : Ω} (hs : s ∈ H.secs) (I : Chart x) :
    s ∈ H.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleDim».«mem_sub_of_mem_secs» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_sub_of_mem_secs_9323478d1234
