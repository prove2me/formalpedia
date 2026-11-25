-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineIdealDual_latticeValue_algebraMap_3a29dedae585
-- name    : P2M_GroundTheory_Heights__Heights_LineIdealDual_latticeValue_algebraMap_3a29dedae585
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:16.001363+00:00
-- url     : https://prove2.me/theorems/59d0a4fd-3e15-5bce-8a81-a708e44dddc1
-- title:
--   P2 M Ground Theory Heights  Heights Line Ideal Dual lattice Value algebra Map 3a29dedae585: P2 M Ground Theory Heights  Heights Line Ideal Dual lattice Value algebra Map 3a29dedae585
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Ideal Dual lattice Value algebra Map 3a29dedae585 construction uses the P2 M Ground Theory Heights  Heights Line Ideal Dual lattice Value algebra Map 3a29dedae585 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineIdealDual.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineIdealDual.lean#L24-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineIdealDual
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
open NumberField Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LineIdealDual

theorem P2M_GroundTheory_Heights__Heights_LineIdealDual_latticeValue_algebraMap_3a29dedae585 {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {m N : ℕ}
    (φ : Fin (N + 1) → Fin m → K) (w : Fin m → K) (b : Fin (N + 1)) :
    latticeValue φ (fun j ↦ algebraMap K K' (w j)) b = algebraMap K K' (φ b ⬝ᵥ w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineIdealDual».«latticeValue_algebraMap» := P2M_GroundTheory_Heights__Heights_LineIdealDual_latticeValue_algebraMap_3a29dedae585
