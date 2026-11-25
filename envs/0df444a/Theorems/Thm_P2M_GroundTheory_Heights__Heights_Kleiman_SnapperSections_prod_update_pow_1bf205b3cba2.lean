-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_prod_update_pow_1bf205b3cba2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_prod_update_pow_1bf205b3cba2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:21:32.120909+00:00
-- url     : https://prove2.me/theorems/d325704b-2ab9-5c21-a54a-a8cbbdc3b799
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Sections prod update pow 1bf205b3cba2: P2 M Ground Theory Heights  Heights Kleiman Snapper Sections prod update pow 1bf205b3cba2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Sections prod update pow 1bf205b3cba2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Sections prod update pow 1bf205b3cba2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L63-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L63-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulQuotEqSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionNonvanishSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutZeroNotLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AssemblyBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperSections
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_prod_update_pow_1bf205b3cba2 {M : Type*} [CommMonoid M] {t : ℕ} (a : Fin t → M) (n : Fin t → ℕ) (j : Fin t) :
    ∏ i, a i ^ Function.update n j (n j + 1) i = (∏ i, a i ^ n i) * a j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperSections».«prod_update_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_prod_update_pow_1bf205b3cba2
