-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepData_form_mem_J_2ff6bfe963bf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepData_form_mem_J_2ff6bfe963bf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:58:57.064613+00:00
-- url     : https://prove2.me/theorems/7e25366d-5825-436e-aaa9-cb57c818caca
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Data form mem J 2ff6bfe963bf: P2 M Ground Theory Heights  Heights Kleiman Step Data form mem J 2ff6bfe963bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Data form mem J 2ff6bfe963bf construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Data form mem J 2ff6bfe963bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L84-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L84-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
variable (T : StepData k x)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepData_form_mem_J_2ff6bfe963bf {f : Poly k N} {e : ℕ} (hf : f ∈ T.J) (he : f.IsHomogeneous e) (I : Chart x)
    {δ : Ω} (hδ : δ ∈ T.D.sub I) : ∃ o ∈ twistMod k x e I, aeval x f * δ = T.si * o := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepData».«form_mem_J» := P2M_GroundTheory_Heights__Heights_Kleiman_StepData_form_mem_J_2ff6bfe963bf
