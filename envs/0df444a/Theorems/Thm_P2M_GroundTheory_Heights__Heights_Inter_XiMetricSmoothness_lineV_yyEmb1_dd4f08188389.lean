-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_lineV_yyEmb1_dd4f08188389
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_lineV_yyEmb1_dd4f08188389
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:53.230745+00:00
-- url     : https://prove2.me/theorems/83726d91-92bf-426b-8f50-64f0c9434ca1
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness line V yy Emb1 dd4f08188389: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness line V yy Emb1 dd4f08188389
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness line V yy Emb1 dd4f08188389 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness line V yy Emb1 dd4f08188389 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L442-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L442-L445

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {D : ℕ} (S : ProjectiveLineBundle D) {N : ℕ} {F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx} {q : ℕ}
  {r : Fin q → MRing S.YIdx} {b : Fin q → T.YBlk → ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_lineV_yyEmb1_dd4f08188389 (z : (Σ k, S.WIdx k) → ℂ) :
    lineV (fun p => z (T.yyEmb 1 p)) = fun k : S.κ => z ⟨.line1, k⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«lineV_yyEmb1» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_lineV_yyEmb1_dd4f08188389
