-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_of_mem_restrictUnion_6649aa89f6fa
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_of_mem_restrictUnion_6649aa89f6fa
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:11:12.139224+00:00
-- url     : https://prove2.me/theorems/9e320130-0054-451b-8668-9d128ba108c6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists mul mem of mem restrict Union 6649aa89f6fa: P2 M Ground Theory Heights  Heights Kleiman exists mul mem of mem restrict Union 6649aa89f6fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists mul mem of mem restrict Union 6649aa89f6fa construction uses the P2 M Ground Theory Heights  Heights Kleiman exists mul mem of mem restrict Union 6649aa89f6fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L34-L42

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_of_mem_restrictUnion_6649aa89f6fa (Q : LineBundle k x) (I J : Chart y) {z : Ω}
    (hz : z ∈ Q.sub (liftChart hxy (restrictUnion I J))) :
    ∃ a ∈ chartRing k x (liftChart hxy I), a ∈ locAt k x y ∧ redAt k x y a ≠ 0 ∧
      a * z ∈ Q.sub (liftChart hxy I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_mul_mem_of_mem_restrictUnion» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_of_mem_restrictUnion_6649aa89f6fa
