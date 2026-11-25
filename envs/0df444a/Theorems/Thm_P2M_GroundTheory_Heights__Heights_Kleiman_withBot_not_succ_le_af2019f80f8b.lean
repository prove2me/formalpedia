-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_withBot_not_succ_le_af2019f80f8b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_withBot_not_succ_le_af2019f80f8b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:03.881415+00:00
-- url     : https://prove2.me/theorems/97dfcfb6-9c10-4583-ab5e-f604f988b9a2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman with Bot not succ le af2019f80f8b: P2 M Ground Theory Heights  Heights Kleiman with Bot not succ le af2019f80f8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman with Bot not succ le af2019f80f8b construction uses the P2 M Ground Theory Heights  Heights Kleiman with Bot not succ le af2019f80f8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L73-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCycleSplit
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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_withBot_not_succ_le_af2019f80f8b {a b : WithBot ℕ∞} (ha : a = ((1 + 1 : ℕ) : WithBot ℕ∞)) (hab : a + 1 ≤ b)
    (hb : b ≤ 2) : False := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«withBot_not_succ_le» := P2M_GroundTheory_Heights__Heights_Kleiman_withBot_not_succ_le_af2019f80f8b
