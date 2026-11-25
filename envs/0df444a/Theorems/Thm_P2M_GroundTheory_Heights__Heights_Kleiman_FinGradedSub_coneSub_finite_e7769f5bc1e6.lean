-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSub_finite_e7769f5bc1e6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSub_finite_e7769f5bc1e6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:06:32.390264+00:00
-- url     : https://prove2.me/theorems/47e71768-c392-48d1-9a1b-f323869d9471
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cone Sub finite e7769f5bc1e6: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cone Sub finite e7769f5bc1e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cone Sub finite e7769f5bc1e6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cone Sub finite e7769f5bc1e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L201-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L201-L221

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
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
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSub_finite_e7769f5bc1e6 : Module.Finite (Poly S N) M.coneSub := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«coneSub_finite» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSub_finite_e7769f5bc1e6
