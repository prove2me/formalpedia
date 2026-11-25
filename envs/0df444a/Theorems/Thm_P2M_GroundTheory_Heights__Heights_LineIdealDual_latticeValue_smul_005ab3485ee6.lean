-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineIdealDual_latticeValue_smul_005ab3485ee6
-- name    : P2M_GroundTheory_Heights__Heights_LineIdealDual_latticeValue_smul_005ab3485ee6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:51.092838+00:00
-- url     : https://prove2.me/theorems/582b189d-579e-5fd6-be0f-89b51ca8f5d9
-- title:
--   P2 M Ground Theory Heights  Heights Line Ideal Dual lattice Value smul 005ab3485ee6: P2 M Ground Theory Heights  Heights Line Ideal Dual lattice Value smul 005ab3485ee6
-- statement:
--   The P2 M Ground Theory Heights  Heights Line Ideal Dual lattice Value smul 005ab3485ee6 construction uses the P2 M Ground Theory Heights  Heights Line Ideal Dual lattice Value smul 005ab3485ee6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineIdealDual.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineIdealDual.lean#L18-L22

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

theorem P2M_GroundTheory_Heights__Heights_LineIdealDual_latticeValue_smul_005ab3485ee6 {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {m N : ℕ}
    (φ : Fin (N + 1) → Fin m → K) (a : K') (v : Fin m → K') (b : Fin (N + 1)) :
    latticeValue φ (a • v) b = a * latticeValue φ v b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LineIdealDual».«latticeValue_smul» := P2M_GroundTheory_Heights__Heights_LineIdealDual_latticeValue_smul_005ab3485ee6
