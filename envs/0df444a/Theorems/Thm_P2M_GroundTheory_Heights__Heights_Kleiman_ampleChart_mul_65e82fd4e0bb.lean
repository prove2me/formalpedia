-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_mul_65e82fd4e0bb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_mul_65e82fd4e0bb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:09:23.48875+00:00
-- url     : https://prove2.me/theorems/fdfb2cc5-9222-44b3-a3e5-8ca5e4af6bd5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ample Chart mul 65e82fd4e0bb: P2 M Ground Theory Heights  Heights Kleiman ample Chart mul 65e82fd4e0bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ample Chart mul 65e82fd4e0bb construction uses the P2 M Ground Theory Heights  Heights Kleiman ample Chart mul 65e82fd4e0bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L82-L92

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_mul_65e82fd4e0bb {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x} {z₁ z₂ : Ω}
    (h₁ : z₁ ∈ ampleChart H m hh I) (h₂ : z₂ ∈ ampleChart H m hh I) :
    z₁ * z₂ ∈ ampleChart H m hh I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ampleChart_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_ampleChart_mul_65e82fd4e0bb
