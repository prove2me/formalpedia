-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_6462ffb5cff7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_6462ffb5cff7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:25.234868+00:00
-- url     : https://prove2.me/theorems/31f5bf0b-1ceb-477b-834c-0e705af9027f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Point Generated mem sub iff 6462ffb5cff7: P2 M Ground Theory Heights  Heights Kleiman Point Generated mem sub iff 6462ffb5cff7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Point Generated mem sub iff 6462ffb5cff7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Point Generated mem sub iff 6462ffb5cff7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointGenerated.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPointGenerated.lean#L59-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPointGenerated
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
open GroundTheory.Heights₂.Heights.Kleiman.PointGenerated
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_6462ffb5cff7 (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) (I J : Chart x)
    (y : Ω) : y ∈ Q.sub I ↔ y ∈ Q.sub J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«PointGenerated».«mem_sub_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_6462ffb5cff7
