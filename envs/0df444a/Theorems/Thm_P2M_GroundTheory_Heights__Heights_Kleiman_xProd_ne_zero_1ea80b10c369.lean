-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_xProd_ne_zero_1ea80b10c369
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_xProd_ne_zero_1ea80b10c369
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:01.396053+00:00
-- url     : https://prove2.me/theorems/78fbb054-825a-4f71-9b90-4e1ecdde4355
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman x Prod ne zero 1ea80b10c369: P2 M Ground Theory Heights  Heights Kleiman x Prod ne zero 1ea80b10c369
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman x Prod ne zero 1ea80b10c369 construction uses the P2 M Ground Theory Heights  Heights Kleiman x Prod ne zero 1ea80b10c369 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L20-L21

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_xProd_ne_zero_1ea80b10c369 (I : Chart x) : xProd I ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«xProd_ne_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_xProd_ne_zero_1ea80b10c369
