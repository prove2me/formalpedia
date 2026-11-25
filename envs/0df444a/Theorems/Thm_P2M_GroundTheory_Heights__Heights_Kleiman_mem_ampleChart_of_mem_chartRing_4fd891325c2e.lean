-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_ampleChart_of_mem_chartRing_4fd891325c2e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_mem_ampleChart_of_mem_chartRing_4fd891325c2e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:59.631802+00:00
-- url     : https://prove2.me/theorems/9918792a-76e2-5c6d-ad78-dc202dc85340
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman mem ample Chart of mem chart Ring 4fd891325c2e: P2 M Ground Theory Heights  Heights Kleiman mem ample Chart of mem chart Ring 4fd891325c2e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman mem ample Chart of mem chart Ring 4fd891325c2e construction uses the P2 M Ground Theory Heights  Heights Kleiman mem ample Chart of mem chart Ring 4fd891325c2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleTwistGenerated.lean#L94-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
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
open scoped Pointwise
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_mem_ampleChart_of_mem_chartRing_4fd891325c2e {H : SubSystem k x Ω} {m : ℕ} {hh : Ω} {I : Chart x}
    {c : Ω} (hc : c ∈ chartRing k x I) : c ∈ ampleChart H m hh I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«mem_ampleChart_of_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_mem_ampleChart_of_mem_chartRing_4fd891325c2e
