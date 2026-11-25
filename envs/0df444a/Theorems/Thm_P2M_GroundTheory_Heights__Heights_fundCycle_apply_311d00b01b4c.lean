-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fundCycle_apply_311d00b01b4c
-- name    : P2M_GroundTheory_Heights__Heights_fundCycle_apply_311d00b01b4c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:33.571739+00:00
-- url     : https://prove2.me/theorems/1c51231b-cc47-4026-8137-ec15eec500a5
-- title:
--   P2 M Ground Theory Heights  Heights fund Cycle apply 311d00b01b4c: P2 M Ground Theory Heights  Heights fund Cycle apply 311d00b01b4c
-- statement:
--   The P2 M Ground Theory Heights  Heights fund Cycle apply 311d00b01b4c construction uses the P2 M Ground Theory Heights  Heights fund Cycle apply 311d00b01b4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L86-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFundCycleBaseChange
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

theorem P2M_GroundTheory_Heights__Heights_fundCycle_apply_311d00b01b4c {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (J W : Ideal (MvPolynomial (Fin n) R)) [Decidable (W ∈ relComps J)] :
    fundCycle J W = if W ∈ relComps J then localMult J W else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fundCycle_apply» := P2M_GroundTheory_Heights__Heights_fundCycle_apply_311d00b01b4c
