-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_eq_mul_of_le_2bf3338d8737
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_eq_mul_of_le_2bf3338d8737
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:53:35.566925+00:00
-- url     : https://prove2.me/theorems/ab05e6bd-f270-4e90-947f-13010c49d68f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cut One Generator exists eq mul of le 2bf3338d8737: P2 M Ground Theory Heights  Heights Kleiman Cut One Generator exists eq mul of le 2bf3338d8737
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cut One Generator exists eq mul of le 2bf3338d8737 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cut One Generator exists eq mul of le 2bf3338d8737 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutOneGenerator.lean#L81-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutOneGenerator.lean#L81-L103

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_eq_mul_of_le_2bf3338d8737 (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {s : Ω} (hs : s ∈ Q.sub (liftChart hxy J))
    (hle : Q.sub (liftChart hxy J) ≤ (Q.twist (idealSys x pp)).sub (liftChart hxy J) ⊔
      Submodule.span (chartRing k x (liftChart hxy J)) {s}) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ b ∈ chartRing k y J, t = b * ρ s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CutOneGenerator».«exists_eq_mul_of_le» := P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_eq_mul_of_le_2bf3338d8737
