-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_restrict_mul_4a5c4ef82f99
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_restrict_mul_4a5c4ef82f99
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:19:21.052855+00:00
-- url     : https://prove2.me/theorems/da5f8795-7e98-4011-8af8-a2205ebcac1f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cut One Generator exists restrict mul 4a5c4ef82f99: P2 M Ground Theory Heights  Heights Kleiman Cut One Generator exists restrict mul 4a5c4ef82f99
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cut One Generator exists restrict mul 4a5c4ef82f99 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cut One Generator exists restrict mul 4a5c4ef82f99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutOneGenerator.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutOneGenerator.lean#L42-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GlobalFunctionsIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutOneGenerator
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
open GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {Q : SubSystem k x Ω} {Q' : SubSystem k y K'} {ρ : Ω → K'}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_restrict_mul_4a5c4ef82f99 (hR : RestrictData Q hxy Q' ρ) (J : Chart y) {c q : Ω}
    (hc : c ∈ chartRing k x (liftChart hxy J)) (hq : q ∈ Q.sub (liftChart hxy J)) :
    ∃ b ∈ chartRing k y J, ρ (c * q) = b * ρ q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CutOneGenerator».«exists_restrict_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_restrict_mul_4a5c4ef82f99
