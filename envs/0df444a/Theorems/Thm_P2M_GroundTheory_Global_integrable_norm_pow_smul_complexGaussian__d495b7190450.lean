-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_integrable_norm_pow_smul_complexGaussian__d495b7190450
-- name    : P2M_GroundTheory_Global_integrable_norm_pow_smul_complexGaussian__d495b7190450
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:49.670484+00:00
-- url     : https://prove2.me/theorems/79795ba1-bef4-4423-82b6-08eec124f103
-- title:
--   P2 M Ground Theory Global integrable norm pow smul complex Gaussian  d495b7190450: P2 M Ground Theory Global integrable norm pow smul complex Gaussian  d495b7190450
-- statement:
--   The P2 M Ground Theory Global integrable norm pow smul complex Gaussian  d495b7190450 construction uses the P2 M Ground Theory Global integrable norm pow smul complex Gaussian  d495b7190450 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L93-L95

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

theorem P2M_GroundTheory_Global_integrable_norm_pow_smul_complexGaussian__d495b7190450 (m : ℤ) (k : ℕ) :
    Integrable (fun z : ℂ ↦ (‖z‖ ^ k : ℝ) • complexGaussian m z) complexPlaceMeasure := by sorry

alias «GroundTheory».«Global».«integrable_norm_pow_smul_complexGaussian'» := P2M_GroundTheory_Global_integrable_norm_pow_smul_complexGaussian__d495b7190450
