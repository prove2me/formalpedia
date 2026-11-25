-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_good_yyEmb_1a6c398b5953
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_good_yyEmb_1a6c398b5953
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:40.807529+00:00
-- url     : https://prove2.me/theorems/90687c12-2384-46f2-a516-04f8878bb2c8
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness good yy Emb 1a6c398b5953: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness good yy Emb 1a6c398b5953
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness good yy Emb 1a6c398b5953 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness good yy Emb 1a6c398b5953 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L447-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L447-L457

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

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_good_yyEmb_1a6c398b5953 {z : (Σ k, S.WIdx k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (j : Fin 2) :
    ∀ k, ∃ i, (fun p => z (T.yyEmb j p)) ⟨k, i⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«good_yyEmb» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_good_yyEmb_1a6c398b5953
