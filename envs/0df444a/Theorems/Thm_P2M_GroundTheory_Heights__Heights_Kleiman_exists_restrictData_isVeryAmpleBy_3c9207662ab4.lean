-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrictData_isVeryAmpleBy_3c9207662ab4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrictData_isVeryAmpleBy_3c9207662ab4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:59.338961+00:00
-- url     : https://prove2.me/theorems/a351bfd2-a063-54f1-b04d-653789c646e8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists restrict Data is Very Ample By 3c9207662ab4: P2 M Ground Theory Heights  Heights Kleiman exists restrict Data is Very Ample By 3c9207662ab4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists restrict Data is Very Ample By 3c9207662ab4 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists restrict Data is Very Ample By 3c9207662ab4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestriction.lean#L21-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestriction.lean#L21-L222

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrictData_isVeryAmpleBy_3c9207662ab4 (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I₀ : Chart y) (Nb : LineBundle k x) {r : ℕ}
    (h : Fin (r + 1) → Ω) (hV : IsVeryAmpleBy Nb.toSubSystem h) :
    ∃ (Q' : LineBundle k y) (ρ : Ω → K'), RestrictData Nb.toSubSystem hxy Q'.toSubSystem ρ ∧
      IsVeryAmpleBy Q'.toSubSystem (ρ ∘ h) ∧ dimCl k y = dimCl k (ρ ∘ h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_restrictData_isVeryAmpleBy» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrictData_isVeryAmpleBy_3c9207662ab4
