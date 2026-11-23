-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- name    : P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:33.307343+00:00
-- url     : https://prove2.me/theorems/26973e12-114d-4464-b822-5a79db1ca732
-- title:
--   P2 M Ground Theory Global trace Form  apply f7b017a4f6bf: P2 M Ground Theory Global trace Form  apply f7b017a4f6bf
-- statement:
--   The P2 M Ground Theory Global trace Form  apply f7b017a4f6bf construction uses the P2 M Ground Theory Global trace Form  apply f7b017a4f6bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L14-L15

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal
noncomputable section

theorem P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf (z w : ℂ) : traceFormℂ z w = 2 * (z * w).re := by sorry

alias «GroundTheory».«Global».«traceFormℂ_apply» := P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
