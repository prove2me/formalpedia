-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_ampleBase_le_chartRing_2377a54c4d9f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_ampleBase_le_chartRing_2377a54c4d9f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:01:17.351397+00:00
-- url     : https://prove2.me/theorems/38bf8dd1-d8d0-4231-8cea-0cbd477518c7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring ample Base le chart Ring 2377a54c4d9f: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring ample Base le chart Ring 23
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring ample Base le chart Ring 2377a54c4d9f construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZChart Ring ample Base le chart Ring 2377a54c4d9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartRing.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZChartRing.lean#L49-L53

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_ampleBase_le_chartRing_2377a54c4d9f {r : ℕ} {h : Fin (r + 1) → Ω} (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) :
    ampleBase (S := S) h j ≤ chartRing S h J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZChartRing».«ampleBase_le_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_ampleBase_le_chartRing_2377a54c4d9f
