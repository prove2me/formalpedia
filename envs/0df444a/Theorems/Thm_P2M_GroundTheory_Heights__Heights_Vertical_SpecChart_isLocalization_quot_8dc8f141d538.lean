-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_isLocalization_quot_8dc8f141d538
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_isLocalization_quot_8dc8f141d538
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:43.255798+00:00
-- url     : https://prove2.me/theorems/f6c1ca73-3417-44b6-9ffb-e0589bc09759
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart is Localization quot 8dc8f141d538: P2 M Ground Theory Heights  Heights Vertical Spec Chart is Localization quot 8dc8f141d538
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart is Localization quot 8dc8f141d538 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart is Localization quot 8dc8f141d538 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartQuot.lean#L12-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartQuot.lean#L12-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {A : Type*} [CommRing A] (W : Ideal A) [W.IsPrime] (P : Ideal A)

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_isLocalization_quot_8dc8f141d538 :
    IsLocalization (W.primeCompl.map (Ideal.Quotient.mk P))
      (Localization.AtPrime W ⧸ P.map (algebraMap A (Localization.AtPrime W))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«isLocalization_quot» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_isLocalization_quot_8dc8f141d538
