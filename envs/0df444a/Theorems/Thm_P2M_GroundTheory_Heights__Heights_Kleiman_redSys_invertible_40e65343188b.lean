-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_invertible_40e65343188b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redSys_invertible_40e65343188b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:32.033834+00:00
-- url     : https://prove2.me/theorems/94ca1bcc-6d47-4ae7-964a-6f6a75e55e89
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red Sys invertible 40e65343188b: P2 M Ground Theory Heights  Heights Kleiman red Sys invertible 40e65343188b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red Sys invertible 40e65343188b construction uses the P2 M Ground Theory Heights  Heights Kleiman red Sys invertible 40e65343188b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L135-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L135-L172

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redSys_invertible_40e65343188b (hγ0 : γ ≠ 0) (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y)
    (hb : ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
      b * γ ∈ Q.sub (liftChart hxy I)) :
    ∃ M' : Submodule (chartRing k y I) K', (redSys hxy Q.toSubSystem γ).sub I * M' = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redSys_invertible» := P2M_GroundTheory_Heights__Heights_Kleiman_redSys_invertible_40e65343188b
