-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_redAt_isUnit_of_isUnit_e99246644bde
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_redAt_isUnit_of_isUnit_e99246644bde
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:12:38.832441+00:00
-- url     : https://prove2.me/theorems/67ae483d-35cb-4f11-a015-82ba21091938
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman red At is Unit of is Unit e99246644bde: P2 M Ground Theory Heights  Heights Kleiman red At is Unit of is Unit e99246644bde
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman red At is Unit of is Unit e99246644bde construction uses the P2 M Ground Theory Heights  Heights Kleiman red At is Unit of is Unit e99246644bde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L23-L32

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_redAt_isUnit_of_isUnit_e99246644bde {I J : Chart y} (h : I.1 ⊆ J.1)
    (a : chartRing k x (liftChart hxy I))
    (ha : IsUnit (chartIncl (S := k) (x := x) (I := liftChart hxy I) (J := liftChart hxy J) h a)) :
    (a : Ω) ∈ locAt k x y ∧ ∃ b ∈ chartRing k y J, redAt k x y a * b = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«redAt_isUnit_of_isUnit» := P2M_GroundTheory_Heights__Heights_Kleiman_redAt_isUnit_of_isUnit_e99246644bde
