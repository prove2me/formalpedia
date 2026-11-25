-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_prod_mem_pow_0b58dec346df
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_prod_mem_pow_0b58dec346df
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:00:52.691642+00:00
-- url     : https://prove2.me/theorems/112deca0-6564-56aa-b093-524bb95e21f4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ZChart Local prod mem pow 0b58dec346df: P2 M Ground Theory Heights  Heights Kleiman ZChart Local prod mem pow 0b58dec346df
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ZChart Local prod mem pow 0b58dec346df construction uses the P2 M Ground Theory Heights  Heights Kleiman ZChart Local prod mem pow 0b58dec346df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PZChartLocal.lean#L39-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZChartLocal
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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.ZChartLocal
open AmpleAffineGen AmpleTwistLocal
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_prod_mem_pow_0b58dec346df (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ZChartLocal».«prod_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_ZChartLocal_prod_mem_pow_0b58dec346df
