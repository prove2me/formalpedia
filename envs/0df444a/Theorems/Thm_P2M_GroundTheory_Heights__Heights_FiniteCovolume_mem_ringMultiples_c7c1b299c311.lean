-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_ringMultiples_c7c1b299c311
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_ringMultiples_c7c1b299c311
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:53.31741+00:00
-- url     : https://prove2.me/theorems/7b1a7ed7-7d82-5ad1-8097-077906df96c6
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume mem ring Multiples c7c1b299c311: P2 M Ground Theory Heights  Heights Finite Covolume mem ring Multiples c7c1b299c311
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume mem ring Multiples c7c1b299c311 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume mem ring Multiples c7c1b299c311 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L32-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceUnitsFiniteIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
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
open scoped Pointwise
noncomputable section
variable {E : Type*} [Field E] [NumberField E] {W : Type*} [AddCommGroup W] [Module E W]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_ringMultiples_c7c1b299c311 {x y : W} : y ∈ ringMultiples E x ↔ ∃ a : 𝓞 E, (a : E) • x = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«mem_ringMultiples» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_ringMultiples_c7c1b299c311
