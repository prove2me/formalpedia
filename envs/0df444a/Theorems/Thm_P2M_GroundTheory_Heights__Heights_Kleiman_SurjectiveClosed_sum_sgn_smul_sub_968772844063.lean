-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_smul_sub_968772844063
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_smul_sub_968772844063
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:22:59.414488+00:00
-- url     : https://prove2.me/theorems/c8aaade4-396a-59c6-8dc1-d16b80a34056
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sum sgn smul sub 968772844063: P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sum sgn smul sub 968772844063
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sum sgn smul sub 968772844063 construction uses the P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sum sgn smul sub 968772844063 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L47-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
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
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {n : ℕ}
variable {U : Finset (Fin n)} {A : Type*} [AddCommGroup A]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_smul_sub_968772844063 (φ : Cell U → A) (J : Cech.Idx U 1) :
    ∑ j : J.1.1, Cech.sgn J.1.1 j • (φ (Cech.face J j).1 - φ J.1) =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • φ (Cech.face J j).1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SurjectiveClosed».«sum_sgn_smul_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_smul_sub_968772844063
