-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_normMatrix_row_f46db8660ccd
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_normMatrix_row_f46db8660ccd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:43.308905+00:00
-- url     : https://prove2.me/theorems/e94a8139-7fa6-4f8a-92e7-9e9e339ff332
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm norm Matrix row f46db8660ccd: P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm norm Matrix row f46db8660ccd
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm norm Matrix row f46db8660ccd construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm norm Matrix row f46db8660ccd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesNorm.lean#L89-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesNorm.lean#L89-L124

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_normMatrix_row_f46db8660ccd (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r)
    (hF : IntSeriesConv F r) {p : ℕ} [NeZero p] (s : ℂ) (hs : ‖s‖ ≤ r) (i : Fin p) :
    ∑ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) * s ^ (k : ℕ) =
      s ^ (i : ℕ) * intSeriesEval F s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«IntSeriesNorm».«normMatrix_row» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_normMatrix_row_f46db8660ccd
