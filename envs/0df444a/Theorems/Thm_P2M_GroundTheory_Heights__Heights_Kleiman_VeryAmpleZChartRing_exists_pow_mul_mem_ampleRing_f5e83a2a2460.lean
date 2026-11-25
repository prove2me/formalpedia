-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_exists_pow_mul_mem_ampleRing_f5e83a2a2460
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_exists_pow_mul_mem_ampleRing_f5e83a2a2460
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:02:08.28369+00:00
-- url     : https://prove2.me/theorems/bbb40839-961e-54e4-a556-d755bbb823a1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring exists pow mul mem ample Ring f5e83a2a2460: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring exists pow mul mem amp
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring exists pow mul mem ample Ring f5e83a2a2460 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring exists pow mul mem ample Ring f5e83a2a2460 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartRing.lean#L19-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartRing.lean#L19-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZChartRing
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartRing
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_exists_pow_mul_mem_ampleRing_f5e83a2a2460 (H : LineBundle S x) {m : ℕ} {h : Ω}
    (hh : ∀ I, h ∈ (H.pow m).sub I) {c : Ω} (hc : c ∈ ampleRing H.toSubSystem m h) (K : Chart x)
    (hrat : ∀ I : Chart x, ∃ e : ℕ,
      c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem m h I)
    {y : Ω} (hy : y ∈ ampleChart H.toSubSystem m h K) : ∃ M : ℕ, c ^ M * y ∈ ampleRing H.toSubSystem m h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZChartRing».«exists_pow_mul_mem_ampleRing» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_exists_pow_mul_mem_ampleRing_f5e83a2a2460
