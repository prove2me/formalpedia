-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChartDimLt_exists_dim_add_card_le_8c654dd77c53
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChartDimLt_exists_dim_add_card_le_8c654dd77c53
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:05:36.807808+00:00
-- url     : https://prove2.me/theorems/eb3bdf7e-e68c-5905-bd8f-f8fb6e2c1104
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Chart Dim Lt exists dim add card le 8c654dd77c53: P2 M Ground Theory Heights  Heights Hilbert Samuel Chart Dim Lt exists dim add card le 8c654dd77c53
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Chart Dim Lt exists dim add card le 8c654dd77c53 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Chart Dim Lt exists dim add card le 8c654dd77c53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ChartDimLtTorus.lean#L15-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ChartDimLtTorus.lean#L15-L140

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ChartDimLtTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDimLt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChartDimLt_exists_dim_add_card_le_8c654dd77c53 {J : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hJ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal J) (p : (k : K) → ι k)
    (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime] (h𝔮 : ReciprocityTheory.AnForm.R.chartIdeal J p ≤ 𝔮) :
    ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = s ∧
      ((s + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ChartDimLt».«exists_dim_add_card_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChartDimLt_exists_dim_add_card_le_8c654dd77c53
