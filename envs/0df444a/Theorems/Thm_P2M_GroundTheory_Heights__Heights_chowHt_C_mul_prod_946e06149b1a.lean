-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_C_mul_prod_946e06149b1a
-- name    : P2M_GroundTheory_Heights__Heights_chowHt_C_mul_prod_946e06149b1a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:58.853446+00:00
-- url     : https://prove2.me/theorems/3e0afab0-9d83-4f4a-aa7f-580d0bd17f14
-- title:
--   P2 M Ground Theory Heights  Heights chow Ht C mul prod 946e06149b1a: P2 M Ground Theory Heights  Heights chow Ht C mul prod 946e06149b1a
-- statement:
--   The P2 M Ground Theory Heights  Heights chow Ht C mul prod 946e06149b1a construction uses the P2 M Ground Theory Heights  Heights chow Ht C mul prod 946e06149b1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L161-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L161-L186

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_chowHt_C_mul_prod_946e06149b1a (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} {ι : Type*}
    (s : Finset ι) (m d : ι → ℕ) (g : ι → MvPolynomial (Fin k × Fin n) K) (hg : ∀ i ∈ s, g i ≠ 0)
    {c : K} (hc : c ≠ 0) :
    chowHt H k (∑ i ∈ s, m i * d i) (C c * ∏ i ∈ s, g i ^ m i) =
      ∑ i ∈ s, (m i : ℝ) * chowHt H k (d i) (g i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chowHt_C_mul_prod» := P2M_GroundTheory_Heights__Heights_chowHt_C_mul_prod_946e06149b1a
