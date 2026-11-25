-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ord_norm_eq_length_b38d6a2def59
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ord_norm_eq_length_b38d6a2def59
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:06.024801+00:00
-- url     : https://prove2.me/theorems/22103840-a668-434c-a006-0dbefb44b835
-- title:
--   P2 M Ground Theory Heights  Heights Vertical ord norm eq length b38d6a2def59: P2 M Ground Theory Heights  Heights Vertical ord norm eq length b38d6a2def59
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical ord norm eq length b38d6a2def59 construction uses the P2 M Ground Theory Heights  Heights Vertical ord norm eq length b38d6a2def59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormLength.lean#L26-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormLength.lean#L26-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormLength
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
open Module
noncomputable section
variable {R B : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B]

theorem P2M_GroundTheory_Heights__Heights_Vertical_ord_norm_eq_length_b38d6a2def59 {b : B} (hb : Function.Injective (fun x : B => b * x)) :
    Ring.ord R (Algebra.norm R b) = Module.length R (B ⧸ Ideal.span {b}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ord_norm_eq_length» := P2M_GroundTheory_Heights__Heights_Vertical_ord_norm_eq_length_b38d6a2def59
