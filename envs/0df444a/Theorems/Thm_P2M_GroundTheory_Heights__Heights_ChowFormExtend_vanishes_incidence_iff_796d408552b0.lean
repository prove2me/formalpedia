-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:26.32682+00:00
-- url     : https://prove2.me/theorems/de84aad5-fec9-4099-9167-e93dbd7d5d2c
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Extend vanishes incidence iff 796d408552b0: P2 M Ground Theory Heights  Heights Chow Form Extend vanishes incidence iff 796d408552b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Extend vanishes incidence iff 796d408552b0 construction uses the P2 M Ground Theory Heights  Heights Chow Form Extend vanishes incidence iff 796d408552b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L38-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
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
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {F : Type*} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0 (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ)
    (g : MvPolynomial (Fin k × Fin n) F) :
    (∀ u ∈ incidence I k, aeval u g = 0) ↔
      ∀ j, X (Sum.inr j) * rename Sum.inl g ∈ (incidenceIdeal I k).radical := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormExtend».«vanishes_incidence_iff» := P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0
