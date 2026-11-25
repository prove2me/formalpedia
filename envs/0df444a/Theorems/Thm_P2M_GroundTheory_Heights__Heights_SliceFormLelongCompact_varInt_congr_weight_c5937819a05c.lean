-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_varInt_congr_weight_c5937819a05c
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_varInt_congr_weight_c5937819a05c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:16.009801+00:00
-- url     : https://prove2.me/theorems/433b7f0e-6acb-4275-80ff-291745278e12
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact var Int congr weight c5937819a05c: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact var Int congr weight c5937819a05c
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact var Int congr weight c5937819a05c construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact var Int congr weight c5937819a05c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L31-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_varInt_congr_weight_c5937819a05c {J : Ideal (MvPolynomial (Fin n) ℂ)} {f g : (Fin n → ℂ) → ℝ}
    (hfg : ∀ x ∈ zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) : varInt J d f φ = varInt J d g φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«varInt_congr_weight» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_varInt_congr_weight_c5937819a05c
