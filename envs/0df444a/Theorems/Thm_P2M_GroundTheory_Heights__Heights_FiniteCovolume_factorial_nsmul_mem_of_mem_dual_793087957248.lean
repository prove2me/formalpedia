-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_factorial_nsmul_mem_of_mem_dual_793087957248
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_factorial_nsmul_mem_of_mem_dual_793087957248
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:37:27.709426+00:00
-- url     : https://prove2.me/theorems/0d56e53c-b487-4497-841a-159e412a864c
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume factorial nsmul mem of mem dual 793087957248: P2 M Ground Theory Heights  Heights Finite Covolume factorial nsmul mem of mem dual 793087957248
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume factorial nsmul mem of mem dual 793087957248 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume factorial nsmul mem of mem dual 793087957248 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementLattice.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementLattice.lean#L38-L45

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
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_factorial_nsmul_mem_of_mem_dual_793087957248 {h : HermitianForm F E W} {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) {y : W} (hy : y ∈ dualLattice h La) : D.factorial • y ∈ La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«factorial_nsmul_mem_of_mem_dual» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_factorial_nsmul_mem_of_mem_dual_793087957248
