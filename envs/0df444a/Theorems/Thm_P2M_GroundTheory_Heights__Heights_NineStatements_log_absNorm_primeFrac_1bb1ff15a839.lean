-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_primeFrac_1bb1ff15a839
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_primeFrac_1bb1ff15a839
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:49.879748+00:00
-- url     : https://prove2.me/theorems/601f0a69-2da3-4d83-acc0-ef4227eda0ce
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements log abs Norm prime Frac 1bb1ff15a839: P2 M Ground Theory Heights  Heights Nine Statements log abs Norm prime Frac 1bb1ff15a839
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements log abs Norm prime Frac 1bb1ff15a839 construction uses the P2 M Ground Theory Heights  Heights Nine Statements log abs Norm prime Frac 1bb1ff15a839 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L68-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_primeFrac_1bb1ff15a839 (L : Type) [Field L] [NumberField L] (q : ℕ) :
    Real.log (FractionalIdeal.absNorm (primeFrac L q) : ℝ) = Module.finrank ℚ L * Real.log q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«log_absNorm_primeFrac» := P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_primeFrac_1bb1ff15a839
