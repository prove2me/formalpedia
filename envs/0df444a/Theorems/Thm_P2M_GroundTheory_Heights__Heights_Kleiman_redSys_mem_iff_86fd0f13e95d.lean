-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_mem_iff_86fd0f13e95d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redSys_mem_iff_86fd0f13e95d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:24.445464+00:00
-- url     : https://prove2.me/theorems/b39908ad-c9c8-4eef-9f1f-74486cfbaea3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red Sys mem iff 86fd0f13e95d: P2 M Ground Theory Heights  Heights Kleiman red Sys mem iff 86fd0f13e95d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red Sys mem iff 86fd0f13e95d construction uses the P2 M Ground Theory Heights  Heights Kleiman red Sys mem iff 86fd0f13e95d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L115-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L115-L133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LineBundleRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineBundleRestrict
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
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
variable {γ : Ω} {Q : LineBundle k x}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redSys_mem_iff_86fd0f13e95d (hg : RedGood hxy Q.toSubSystem γ) (I J : Chart y) (h : I.1 ⊆ J.1) (z : K') :
    z ∈ (redSys hxy Q.toSubSystem γ).sub J ↔ ∃ c : chartRing k y I, IsUnit (chartIncl h c) ∧
      (c : K') • z ∈ (redSys hxy Q.toSubSystem γ).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redSys_mem_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_redSys_mem_iff_86fd0f13e95d
