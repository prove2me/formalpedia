-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_of_veryAmple_68e58f10b840
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_of_veryAmple_68e58f10b840
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:56.099809+00:00
-- url     : https://prove2.me/theorems/53bde907-a547-4fe7-8948-570bfcd61bba
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman inter Num nonneg of very Ample 68e58f10b840: P2 M Ground Theory Heights  Heights Kleiman inter Num nonneg of very Ample 68e58f10b840
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman inter Num nonneg of very Ample 68e58f10b840 construction uses the P2 M Ground Theory Heights  Heights Kleiman inter Num nonneg of very Ample 68e58f10b840 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L188-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L188-L209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
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
open MvPolynomial Filter
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (hR : GenericPointSectionInput.Statement.{u, w})
include hR

theorem P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_of_veryAmple_68e58f10b840 : ∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x),
    IsSubvar x pp n → (∀ i, IsVeryAmple (L i).toSubSystem) →
      0 ≤ interNum pp (fun i => (L i).toSubSystem) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«interNum_nonneg_of_veryAmple» := P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_of_veryAmple_68e58f10b840
