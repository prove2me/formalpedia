-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_residuePart_conv_7c24ca73e8b7
-- name    : P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_residuePart_conv_7c24ca73e8b7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:55.726441+00:00
-- url     : https://prove2.me/theorems/efa40a8b-a27b-47fc-9e36-7e5ad408e030
-- title:
--   P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm residue Part conv 7c24ca73e8b7: P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm residue Part conv 7c24ca73e8b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm residue Part conv 7c24ca73e8b7 construction uses the P2 M Ground Theory Heights  Heights Chowla Selberg Int Series Norm residue Part conv 7c24ca73e8b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesNorm.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/PIntSeriesNorm.lean#L35-L45

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

theorem P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_residuePart_conv_7c24ca73e8b7 {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r) (hF : IntSeriesConv F r)
    {p : ℕ} (hp : 0 < p) (i : ℕ) : IntSeriesConv (residuePart F p i) (r ^ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowlaSelberg».«IntSeriesNorm».«residuePart_conv» := P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_residuePart_conv_7c24ca73e8b7
