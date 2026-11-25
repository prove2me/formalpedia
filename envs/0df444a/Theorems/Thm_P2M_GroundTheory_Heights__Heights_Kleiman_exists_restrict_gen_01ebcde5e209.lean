-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrict_gen_01ebcde5e209
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrict_gen_01ebcde5e209
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:08:32.022381+00:00
-- url     : https://prove2.me/theorems/eb1b1af9-ee95-4323-ac7b-412ef29980ff
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists restrict gen 01ebcde5e209: P2 M Ground Theory Heights  Heights Kleiman exists restrict gen 01ebcde5e209
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists restrict gen 01ebcde5e209 construction uses the P2 M Ground Theory Heights  Heights Kleiman exists restrict gen 01ebcde5e209 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L44-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L44-L86

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrict_gen_01ebcde5e209 (Q : LineBundle k x) :
    ∃ γ : Ω, γ ≠ 0 ∧ RedGood hxy Q.toSubSystem γ ∧ ∀ I : Chart y,
      ∃ b ∈ chartRing k x (liftChart hxy I), b ∈ locAt k x y ∧ redAt k x y b ≠ 0 ∧
        b * γ ∈ Q.sub (liftChart hxy I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_restrict_gen» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_restrict_gen_01ebcde5e209
