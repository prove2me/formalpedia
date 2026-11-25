-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawBasic_volume_firstRow_mem_1fba3e2dc8f5
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawBasic_volume_firstRow_mem_1fba3e2dc8f5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:18.529248+00:00
-- url     : https://prove2.me/theorems/c4b461a9-bcd8-408d-9017-80b17238cb3a
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law Basic volume first Row mem 1fba3e2dc8f5: P2 M Ground Theory Heights  Heights Sphere Law Basic volume first Row mem 1fba3e2dc8f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law Basic volume first Row mem 1fba3e2dc8f5 construction uses the P2 M Ground Theory Heights  Heights Sphere Law Basic volume first Row mem 1fba3e2dc8f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawBasic.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawBasic.lean#L34-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawBasic
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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawBasic

theorem P2M_GroundTheory_Heights__Heights_SphereLawBasic_volume_firstRow_mem_1fba3e2dc8f5 (N : ℕ) (S : Submodule ℂ (Fin N → ℂ)) (hS : S ≠ ⊤) :
    volume {u : Fin 1 × Fin N → ℂ | firstRow N u ∈ S} = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawBasic».«volume_firstRow_mem» := P2M_GroundTheory_Heights__Heights_SphereLawBasic_volume_firstRow_mem_1fba3e2dc8f5
