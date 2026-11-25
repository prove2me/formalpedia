-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_funField_hom_ext_8fb52f33d4ed
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_funField_hom_ext_8fb52f33d4ed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:07.480539+00:00
-- url     : https://prove2.me/theorems/a6e5a473-ca5a-4b0c-9ad8-0972d1eeaff3
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Embedding holds fun Field hom ext 8fb52f33d4ed: P2 M Ground Theory Heights  Heights Inter regularity Embedding holds fun Field hom ext 8fb52f33d4ed
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Embedding holds fun Field hom ext 8fb52f33d4ed construction uses the P2 M Ground Theory Heights  Heights Inter regularity Embedding holds fun Field hom ext 8fb52f33d4ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L104-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L104-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_funField_hom_ext_8fb52f33d4ed {P : Ideal (MRing ι)} [P.IsPrime] {τ₁ τ₂ : funField P →+* ℂ}
    (h : ∀ (x : funField P) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ P →
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P v = toFrac P u → τ₁ x = τ₂ x) : τ₁ = τ₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityEmbedding_holds».«funField_hom_ext» := P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_funField_hom_ext_8fb52f33d4ed
