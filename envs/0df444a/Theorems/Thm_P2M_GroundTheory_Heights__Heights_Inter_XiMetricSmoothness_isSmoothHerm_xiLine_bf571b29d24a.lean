-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_isSmoothHerm_xiLine_bf571b29d24a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_isSmoothHerm_xiLine_bf571b29d24a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:43.97345+00:00
-- url     : https://prove2.me/theorems/c2e096d7-a7b8-4459-814b-a2a9093909c7
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness is Smooth Herm xi Line bf571b29d24a: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness is Smooth Herm xi Line bf571b29d24a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness is Smooth Herm xi Line bf571b29d24a construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness is Smooth Herm xi Line bf571b29d24a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L415-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L415-L428

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
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {G : YPt ι ν κ → Matrix κ κ ℂ} {N : ℕ}
  {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)} {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_isSmoothHerm_xiLine_bf571b29d24a (hG : IsEEMetric G)
    (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3)))
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0)
    (hcov : ∀ w : YPt ι ν κ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ j, evC (r j) w = 0) → ∃ i l k m, evC (F i l k m) w ≠ 0) :
    IsSmoothHerm (xiLine hG hF hr hrl hcov) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«isSmoothHerm_xiLine» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_isSmoothHerm_xiLine_bf571b29d24a
