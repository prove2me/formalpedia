-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_of_irrelevant_6754bd39d524
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_of_irrelevant_6754bd39d524
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:05:03.738827+00:00
-- url     : https://prove2.me/theorems/9e367bf5-81a0-5253-8bc5-c435ae29425e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys of irrelevant 6754bd39d524: P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys of irrelevant 6754bd39d524
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys of irrelevant 6754bd39d524 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist ideal Sys of irrelevant 6754bd39d524 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L42-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L42-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
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
universe u v w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_of_irrelevant_6754bd39d524 (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) :
    (twistSys k x a).twist (idealSys x pp) = twistSys k x a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_idealSys_of_irrelevant» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_of_irrelevant_6754bd39d524
