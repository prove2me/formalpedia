-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_subSystem_ext_ddefc825c292
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_subSystem_ext_ddefc825c292
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:02:21.715117+00:00
-- url     : https://prove2.me/theorems/f715285f-0c2d-4591-8c66-fba166c458aa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman sub System ext ddefc825c292: P2 M Ground Theory Heights  Heights Kleiman sub System ext ddefc825c292
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman sub System ext ddefc825c292 construction uses the P2 M Ground Theory Heights  Heights Kleiman sub System ext ddefc825c292 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L34-L40

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_subSystem_ext_ddefc825c292 {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    {F G : SubSystem k x E} (h : ∀ I, F.sub I = G.sub I) : F = G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«subSystem_ext» := P2M_GroundTheory_Heights__Heights_Kleiman_subSystem_ext_ddefc825c292
