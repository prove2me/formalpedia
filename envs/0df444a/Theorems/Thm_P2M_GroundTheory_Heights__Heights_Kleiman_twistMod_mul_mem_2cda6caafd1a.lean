-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_mem_2cda6caafd1a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_mem_2cda6caafd1a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:08.253589+00:00
-- url     : https://prove2.me/theorems/2c7c8b5a-e3ef-41d2-ad6a-5a8572f25bf6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Mod mul mem 2cda6caafd1a: P2 M Ground Theory Heights  Heights Kleiman twist Mod mul mem 2cda6caafd1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Mod mul mem 2cda6caafd1a construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Mod mul mem 2cda6caafd1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZeroIdealChart.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZeroIdealChart.lean#L47-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_mem_2cda6caafd1a {K : Chart x} {a b : Ω} {c c' : ℤ} (ha : a ∈ twistMod S x c K)
    (hb : b ∈ twistMod S x c' K) : a * b ∈ twistMod S x (c + c') K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistMod_mul_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_mem_2cda6caafd1a
