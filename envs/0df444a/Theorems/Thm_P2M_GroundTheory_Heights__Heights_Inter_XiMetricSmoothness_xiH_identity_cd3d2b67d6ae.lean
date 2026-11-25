-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_xiH_identity_cd3d2b67d6ae
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_xiH_identity_cd3d2b67d6ae
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:25.979822+00:00
-- url     : https://prove2.me/theorems/f091d99a-ca44-5b67-add2-0a26bafc7395
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness xi H identity cd3d2b67d6ae: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness xi H identity cd3d2b67d6ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness xi H identity cd3d2b67d6ae construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness xi H identity cd3d2b67d6ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L459-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L459-L544

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

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_xiH_identity_cd3d2b67d6ae (hF : S.IsPluckerRel N F) (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0)
    (hrW : ∀ j, rename (T.yyEmb 0) (r j) ∈ S.WW) {z : (Σ k, S.WIdx k) → ℂ} (hz : z ∈ mcPts S.WW) :
    ‖eval z (map (Int.castRingHom ℂ) S.g)‖ ^ 2 * xiH S.G N F r b (fun p => z (T.yyEmb 0 p)) *
        xiH S.G N F r b (fun p => z (T.yyEmb 1 p)) =
      ‖eval z (map (Int.castRingHom ℂ) S.h)‖ ^ 2 *
        sinSqG (S.G fun p => z (T.yyEmb 0 p)) (fun k => z ⟨.line0, k⟩) (fun k => z ⟨.line1, k⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«xiH_identity» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_xiH_identity_cd3d2b67d6ae
