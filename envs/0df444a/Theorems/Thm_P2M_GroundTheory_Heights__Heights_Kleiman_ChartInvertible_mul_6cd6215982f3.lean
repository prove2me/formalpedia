-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:32:14.106367+00:00
-- url     : https://prove2.me/theorems/900b11a7-941f-5bc5-9c93-f89b079a5c45
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Chart Invertible mul 6cd6215982f3: P2 M Ground Theory Heights  Heights Kleiman Chart Invertible mul 6cd6215982f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Chart Invertible mul 6cd6215982f3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Chart Invertible mul 6cd6215982f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepDataJProper.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepDataJProper.lean#L29-L33

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3 {I : Chart x} {P P' : Submodule (chartRing S x I) Ω}
    (h : ChartInvertible P) (h' : ChartInvertible P') : ChartInvertible (P * P') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ChartInvertible».«mul» := P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3
