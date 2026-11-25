-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_laurent_smul_eq_zero_b71283610103
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_laurent_smul_eq_zero_b71283610103
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:27.070338+00:00
-- url     : https://prove2.me/theorems/23df75de-c80d-4c75-bd0b-3a827a0c3499
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman laurent smul eq zero b71283610103: P2 M Ground Theory Heights  Heights Kleiman laurent smul eq zero b71283610103
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman laurent smul eq zero b71283610103 construction uses the P2 M Ground Theory Heights  Heights Kleiman laurent smul eq zero b71283610103 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StepTwoFiltGraded.lean#L94-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded
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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E]
variable {x E}
variable [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_laurent_smul_eq_zero_b71283610103 {p : Poly S N} (hp : p ∈ primeOf (S := S) x) (m : LaurentSpace x E) :
    p • m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«laurent_smul_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_laurent_smul_eq_zero_b71283610103
