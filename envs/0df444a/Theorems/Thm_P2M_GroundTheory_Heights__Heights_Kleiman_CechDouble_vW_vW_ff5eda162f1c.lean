-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_vW_vW_ff5eda162f1c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_vW_vW_ff5eda162f1c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:54:04.459333+00:00
-- url     : https://prove2.me/theorems/d5c2fcb2-0057-4146-991d-b0d311d7acc7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double v W v W ff5eda162f1c: P2 M Ground Theory Heights  Heights Kleiman Cech Double v W v W ff5eda162f1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double v W v W ff5eda162f1c construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double v W v W ff5eda162f1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDouble.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDouble.lean#L124-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDouble
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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble
open Cech
variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {N r : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (r + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_vW_vW_ff5eda162f1c (p q : ℕ) (s : W E x y p q) : vW S E x y (p + 1) q (vW S E x y p q s) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«vW_vW» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_vW_vW_ff5eda162f1c
