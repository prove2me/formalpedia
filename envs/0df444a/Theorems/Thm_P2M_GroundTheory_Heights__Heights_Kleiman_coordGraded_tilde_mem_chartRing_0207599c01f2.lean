-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tilde_mem_chartRing_0207599c01f2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tilde_mem_chartRing_0207599c01f2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:12:41.15818+00:00
-- url     : https://prove2.me/theorems/291b96c3-1619-45e2-b165-259bf255696d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coord Graded tilde mem chart Ring 0207599c01f2: P2 M Ground Theory Heights  Heights Kleiman coord Graded tilde mem chart Ring 0207599c01f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coord Graded tilde mem chart Ring 0207599c01f2 construction uses the P2 M Ground Theory Heights  Heights Kleiman coord Graded tilde mem chart Ring 0207599c01f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L19-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L19-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tilde_mem_chartRing_0207599c01f2 {I : Chart x} {y : Ω}
    (hy : y ∈ (coordGraded k x).tilde 0 I) : y ∈ chartRing k x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coordGraded_tilde_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_tilde_mem_chartRing_0207599c01f2
