-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_ne_zero_of_mem_6daf37f2ffbd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_ne_zero_of_mem_6daf37f2ffbd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:42.448932+00:00
-- url     : https://prove2.me/theorems/6ebf11aa-7f65-52ab-a1a7-cfdb49904076
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman algebra Map ne zero of mem 6daf37f2ffbd: P2 M Ground Theory Heights  Heights Kleiman algebra Map ne zero of mem 6daf37f2ffbd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman algebra Map ne zero of mem 6daf37f2ffbd construction uses the P2 M Ground Theory Heights  Heights Kleiman algebra Map ne zero of mem 6daf37f2ffbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L90-L94

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_ne_zero_of_mem_6daf37f2ffbd (F : Type u) [Field F] [Algebra S F] [Algebra F Ω]
    [IsScalarTower S F Ω] [IsFractionRing S F] {t : S} (ht : t ∈ nonZeroDivisors S) : algebraMap S Ω t ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«algebraMap_ne_zero_of_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_ne_zero_of_mem_6daf37f2ffbd
