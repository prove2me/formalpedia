-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_restrict_twist_eq_zero_e84501a9b4aa
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_restrict_twist_eq_zero_e84501a9b4aa
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:54:17.660128+00:00
-- url     : https://prove2.me/theorems/86ecd7cc-92f1-4cb5-98f2-ca69a9d0f17b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cut One Generator restrict twist eq zero e84501a9b4aa: P2 M Ground Theory Heights  Heights Kleiman Cut One Generator restrict twist eq zero e84501a9b4aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cut One Generator restrict twist eq zero e84501a9b4aa construction uses the P2 M Ground Theory Heights  Heights Kleiman Cut One Generator restrict twist eq zero e84501a9b4aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutOneGenerator.lean#L48-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutOneGenerator.lean#L48-L79

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_restrict_twist_eq_zero_e84501a9b4aa (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {z : Ω}
    (hz : z ∈ (Q.twist (idealSys x pp)).sub (liftChart hxy J)) :
    z ∈ Q.sub (liftChart hxy J) ∧ ρ z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CutOneGenerator».«restrict_twist_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_restrict_twist_eq_zero_e84501a9b4aa
