-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_pow_ff3b4f7f14e7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_pow_ff3b4f7f14e7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:00:31.878822+00:00
-- url     : https://prove2.me/theorems/70f113b0-49cd-4a2f-8714-77a26629aec6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ample Chart pow ff3b4f7f14e7: P2 M Ground Theory Heights  Heights Kleiman ample Chart pow ff3b4f7f14e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ample Chart pow ff3b4f7f14e7 construction uses the P2 M Ground Theory Heights  Heights Kleiman ample Chart pow ff3b4f7f14e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L100-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
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
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_pow_ff3b4f7f14e7 {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z : Ω}
    (hz : z ∈ ampleChart H m hh I) (n : ℕ) : z ^ n ∈ ampleChart H m hh I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ampleChart_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_pow_ff3b4f7f14e7
