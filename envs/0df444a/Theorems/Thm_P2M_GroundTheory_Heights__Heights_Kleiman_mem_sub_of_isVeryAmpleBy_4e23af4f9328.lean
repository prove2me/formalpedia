-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_sub_of_isVeryAmpleBy_4e23af4f9328
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_sub_of_isVeryAmpleBy_4e23af4f9328
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:48.535102+00:00
-- url     : https://prove2.me/theorems/0d02e982-67a9-4eb1-970b-fc41b146e737
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem sub of is Very Ample By 4e23af4f9328: P2 M Ground Theory Heights  Heights Kleiman mem sub of is Very Ample By 4e23af4f9328
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem sub of is Very Ample By 4e23af4f9328 construction uses the P2 M Ground Theory Heights  Heights Kleiman mem sub of is Very Ample By 4e23af4f9328 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L26-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
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
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_sub_of_isVeryAmpleBy_4e23af4f9328 (hV : IsVeryAmpleBy Nb.toSubSystem h) (l : Fin (r + 1)) (I : Chart x) :
    h l ∈ Nb.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_sub_of_isVeryAmpleBy» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_sub_of_isVeryAmpleBy_4e23af4f9328
