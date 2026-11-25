-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_twistMod_11b60f1db303
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_twistMod_11b60f1db303
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:02.197331+00:00
-- url     : https://prove2.me/theorems/608caed2-168a-51af-841b-ed7812c7a9a0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman aeval mem twist Mod 11b60f1db303: P2 M Ground Theory Heights  Heights Kleiman aeval mem twist Mod 11b60f1db303
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman aeval mem twist Mod 11b60f1db303 construction uses the P2 M Ground Theory Heights  Heights Kleiman aeval mem twist Mod 11b60f1db303 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZeroIdealChart.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZeroIdealChart.lean#L28-L30

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_twistMod_11b60f1db303 {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) (K : Chart x) :
    aeval x f ∈ twistMod S x (e : ℤ) K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«aeval_mem_twistMod» := P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_twistMod_11b60f1db303
