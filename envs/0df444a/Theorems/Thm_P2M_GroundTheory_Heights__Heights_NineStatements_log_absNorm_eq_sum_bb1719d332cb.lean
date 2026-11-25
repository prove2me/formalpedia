-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_eq_sum_bb1719d332cb
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_eq_sum_bb1719d332cb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:33.700866+00:00
-- url     : https://prove2.me/theorems/d64bc656-2db1-4bfe-a1c0-2dde309c6acc
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements log abs Norm eq sum bb1719d332cb: P2 M Ground Theory Heights  Heights Nine Statements log abs Norm eq sum bb1719d332cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements log abs Norm eq sum bb1719d332cb construction uses the P2 M Ground Theory Heights  Heights Nine Statements log abs Norm eq sum bb1719d332cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L42-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L42-L66

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

theorem P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_eq_sum_bb1719d332cb {L : Type} [Field L] [NumberField L] {I : FractionalIdeal (𝓞 L)⁰ L}
    (hI : I ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ v, FractionalIdeal.count L v I ≠ 0 → v ∈ T) :
    Real.log (FractionalIdeal.absNorm I : ℝ) =
      ∑ v ∈ T, (FractionalIdeal.count L v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«log_absNorm_eq_sum» := P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_eq_sum_bb1719d332cb
