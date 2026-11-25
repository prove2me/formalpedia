-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_toTildeH_surjective_da8a6cc05bed
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_toTildeH_surjective_da8a6cc05bed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:52.719427+00:00
-- url     : https://prove2.me/theorems/6917d5ea-b94c-5685-8d5e-deb8d51200ed
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman to Tilde H surjective da8a6cc05bed: P2 M Ground Theory Heights  Heights Kleiman to Tilde H surjective da8a6cc05bed
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman to Tilde H surjective da8a6cc05bed construction uses the P2 M Ground Theory Heights  Heights Kleiman to Tilde H surjective da8a6cc05bed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFiniteE.lean#L143-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFiniteE.lean#L143-L150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteESt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFiniteE
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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_toTildeH_surjective_da8a6cc05bed (n : ℕ) : Function.Surjective (toTildeH M c n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«toTildeH_surjective» := P2M_GroundTheory_Heights__Heights_Kleiman_toTildeH_surjective_da8a6cc05bed
