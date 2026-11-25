-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_mem_twist_of_eq_zero_e2a97b30400f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_mem_twist_of_eq_zero_e2a97b30400f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:12:08.450447+00:00
-- url     : https://prove2.me/theorems/7aa28a79-9407-5242-a239-154564ae9fef
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Generated mem twist of eq zero e2a97b30400f: P2 M Ground Theory Heights  Heights Kleiman Restrict Generated mem twist of eq zero e2a97b30400f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Generated mem twist of eq zero e2a97b30400f construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Generated mem twist of eq zero e2a97b30400f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L70-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictGenerated.lean#L70-L117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictGenerated
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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}
  {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_mem_twist_of_eq_zero_e2a97b30400f (Q : LineBundle S x) (Q' : LineBundle S y) {r : Ω → K'}
    {pp : Ideal (Poly S N)} (hpp : primeOf (S := S) y = pp)
    (h : RestrictData Q.toSubSystem hxy Q'.toSubSystem r) (J : Chart y) {z : Ω}
    (hz : z ∈ Q.toSubSystem.sub (liftChart hxy J)) (hr : r z = 0) :
    z ∈ (Q.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictGenerated».«mem_twist_of_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictGenerated_mem_twist_of_eq_zero_e2a97b30400f
