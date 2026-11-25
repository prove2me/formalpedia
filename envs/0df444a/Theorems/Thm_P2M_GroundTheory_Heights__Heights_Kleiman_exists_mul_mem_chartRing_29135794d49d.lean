-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_chartRing_29135794d49d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_chartRing_29135794d49d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:15.366517+00:00
-- url     : https://prove2.me/theorems/85a255f0-40bb-4b77-a0d8-d9912f5e96d7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists mul mem chart Ring 29135794d49d: P2 M Ground Theory Heights  Heights Kleiman exists mul mem chart Ring 29135794d49d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists mul mem chart Ring 29135794d49d construction uses the P2 M Ground Theory Heights  Heights Kleiman exists mul mem chart Ring 29135794d49d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L96-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L96-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
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
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
  [IsFractionRing S F]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_chartRing_29135794d49d {I : Chart x} {a : Ω} (ha : a ∈ chartRing F x I) :
    ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_mul_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_chartRing_29135794d49d
