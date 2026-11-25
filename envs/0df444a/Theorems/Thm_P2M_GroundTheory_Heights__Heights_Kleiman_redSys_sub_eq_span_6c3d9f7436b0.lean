-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_span_6c3d9f7436b0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_span_6c3d9f7436b0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:11:03.736889+00:00
-- url     : https://prove2.me/theorems/72fc330a-9781-56e7-8098-ee8603747f40
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red Sys sub eq span 6c3d9f7436b0: P2 M Ground Theory Heights  Heights Kleiman red Sys sub eq span 6c3d9f7436b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red Sys sub eq span 6c3d9f7436b0 construction uses the P2 M Ground Theory Heights  Heights Kleiman red Sys sub eq span 6c3d9f7436b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L90-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L90-L113

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_span_6c3d9f7436b0 (hg : RedGood hxy Q.toSubSystem γ) (I : Chart y) {s : Set Ω}
    (hs : Submodule.span (chartRing k x (liftChart hxy I)) s = Q.sub (liftChart hxy I)) :
    (redSys hxy Q.toSubSystem γ).sub I =
      Submodule.span (chartRing k y I) ((fun q => redAt k x y (q / γ)) '' s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redSys_sub_eq_span» := P2M_GroundTheory_Heights__Heights_Kleiman_redSys_sub_eq_span_6c3d9f7436b0
