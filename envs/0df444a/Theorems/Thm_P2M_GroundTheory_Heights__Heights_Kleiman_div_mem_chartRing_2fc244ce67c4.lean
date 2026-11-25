-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_div_mem_chartRing_2fc244ce67c4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_div_mem_chartRing_2fc244ce67c4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:03:01.164554+00:00
-- url     : https://prove2.me/theorems/666c3b4a-d801-59e4-b49a-362d3320f524
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman div mem chart Ring 2fc244ce67c4: P2 M Ground Theory Heights  Heights Kleiman div mem chart Ring 2fc244ce67c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman div mem chart Ring 2fc244ce67c4 construction uses the P2 M Ground Theory Heights  Heights Kleiman div mem chart Ring 2fc244ce67c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimSeq.lean#L72-L80

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_div_mem_chartRing_2fc244ce67c4 {e : ℕ} (I : Chart x) {o : Ω} (ho : o ∈ twistMod k x e I) {s : Poly k N}
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) : o / aeval x s ∈ chartRing k x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«div_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_div_mem_chartRing_2fc244ce67c4
