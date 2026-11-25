-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ballProd_subset_polydisc_122db61ad4e0
-- name    : P2M_GroundTheory_Heights__Heights_ballProd_subset_polydisc_122db61ad4e0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:10.155867+00:00
-- url     : https://prove2.me/theorems/9bb925b1-5b29-5d69-9c5f-f6f0356cd562
-- title:
--   P2 M Ground Theory Heights  Heights ball Prod subset polydisc 122db61ad4e0: P2 M Ground Theory Heights  Heights ball Prod subset polydisc 122db61ad4e0
-- statement:
--   The P2 M Ground Theory Heights  Heights ball Prod subset polydisc 122db61ad4e0 construction uses the P2 M Ground Theory Heights  Heights ball Prod subset polydisc 122db61ad4e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PMahlerIntegrand.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PMahlerIntegrand.lean#L10-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMahlerIntegrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory

theorem P2M_GroundTheory_Heights__Heights_ballProd_subset_polydisc_122db61ad4e0 {n k : ℕ} (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballProd h k ⊆ LogInt.polydisc _ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ballProd_subset_polydisc» := P2M_GroundTheory_Heights__Heights_ballProd_subset_polydisc_122db61ad4e0
