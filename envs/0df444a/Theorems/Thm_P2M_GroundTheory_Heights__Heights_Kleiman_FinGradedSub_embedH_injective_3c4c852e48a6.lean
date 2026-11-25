-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedH_injective_3c4c852e48a6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedH_injective_3c4c852e48a6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:21.008809+00:00
-- url     : https://prove2.me/theorems/7456f853-4121-5f59-8997-3c6cfd04a621
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub embed H injective 3c4c852e48a6: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub embed H injective 3c4c852e48a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub embed H injective 3c4c852e48a6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub embed H injective 3c4c852e48a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L222-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L222-L244

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
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
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedH_injective_3c4c852e48a6 (n : ℕ) : Function.Injective (M.embedH c n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«embedH_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedH_injective_3c4c852e48a6
