-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_incIdeal_iffR_6f31959e16f5
-- name    : P2M_GroundTheory_Heights__Heights_mem_incIdeal_iffR_6f31959e16f5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:16.163426+00:00
-- url     : https://prove2.me/theorems/ab1209b8-1a09-4ca7-8eca-d4e9d0602acc
-- title:
--   P2 M Ground Theory Heights  Heights mem inc Ideal iff R 6f31959e16f5: P2 M Ground Theory Heights  Heights mem inc Ideal iff R 6f31959e16f5
-- statement:
--   The P2 M Ground Theory Heights  Heights mem inc Ideal iff R 6f31959e16f5 construction uses the P2 M Ground Theory Heights  Heights mem inc Ideal iff R 6f31959e16f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormReduced.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormReduced.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncIdealSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormReduced
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
variable {F : Type*} [Field F] {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_mem_incIdeal_iffR_6f31959e16f5 {P : Ideal (MvPolynomial (Fin n) F)} {g : MvPolynomial (Fin k × Fin n) F} :
    g ∈ incIdeal P k ↔ ∀ u ∈ incidence P k, aeval u g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_incIdeal_iffR» := P2M_GroundTheory_Heights__Heights_mem_incIdeal_iffR_6f31959e16f5
