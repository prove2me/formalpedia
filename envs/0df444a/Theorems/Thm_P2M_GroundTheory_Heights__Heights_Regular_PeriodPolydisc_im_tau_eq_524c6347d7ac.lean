-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_im_tau_eq_524c6347d7ac
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_im_tau_eq_524c6347d7ac
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:17:40.864876+00:00
-- url     : https://prove2.me/theorems/a1cfc123-d6da-4abe-81f0-f732214caba0
-- title:
--   P2 M Ground Theory Heights  Heights Regular Period Polydisc im tau eq 524c6347d7ac: P2 M Ground Theory Heights  Heights Regular Period Polydisc im tau eq 524c6347d7ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Period Polydisc im tau eq 524c6347d7ac construction uses the P2 M Ground Theory Heights  Heights Regular Period Polydisc im tau eq 524c6347d7ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L153-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PImTauBounds.lean#L153-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PImTauBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)

theorem P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_im_tau_eq_524c6347d7ac {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hT0 : P.IsTau0Ext T0)
    {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) :
    (P.τ w).map Complex.im = (T0 (expCover a w)).map Complex.im +
      ∑ i : Fin a, (-(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)) • P.realB i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PeriodPolydisc».«im_tau_eq» := P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_im_tau_eq_524c6347d7ac
