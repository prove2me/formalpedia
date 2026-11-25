-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartInvertible_twistMul_744ff127a3f7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_chartInvertible_twistMul_744ff127a3f7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:36.198099+00:00
-- url     : https://prove2.me/theorems/ba453d92-d6e3-51eb-a09b-47be23fb35be
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman chart Invertible twist Mul 744ff127a3f7: P2 M Ground Theory Heights  Heights Kleiman chart Invertible twist Mul 744ff127a3f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman chart Invertible twist Mul 744ff127a3f7 construction uses the P2 M Ground Theory Heights  Heights Kleiman chart Invertible twist Mul 744ff127a3f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepDataJProper.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepDataJProper.lean#L39-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
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
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_chartInvertible_twistMul_744ff127a3f7 (M : LineBundle S x) (p : ℕ) (m : ℤ) (I : Chart x) :
    ChartInvertible ((twistMul M.toSubSystem p m).sub I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«chartInvertible_twistMul» := P2M_GroundTheory_Heights__Heights_Kleiman_chartInvertible_twistMul_744ff127a3f7
