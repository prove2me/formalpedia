-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_prod_ne_zero_82f3e7b02aa9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_prod_ne_zero_82f3e7b02aa9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:53.399797+00:00
-- url     : https://prove2.me/theorems/5538bcca-c5ba-4de3-8df7-102ed1cfbcd0
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Embedding holds to Frac prod ne zero 82f3e7b02aa9: P2 M Ground Theory Heights  Heights Inter regularity Embedding holds to Frac prod ne zero 82f3e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Embedding holds to Frac prod ne zero 82f3e7b02aa9 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Embedding holds to Frac prod ne zero 82f3e7b02aa9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L135-L139

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_prod_ne_zero_82f3e7b02aa9 {P : Ideal (MRing ι)} [P.IsPrime] (j : ∀ k, ι k)
    (hj : ∀ k, (X ⟨k, j k⟩ : MRing ι) ∉ P) (a : K → ℕ) :
    toFrac P (∏ k, (X ⟨k, j k⟩ : MRing ι) ^ a k) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityEmbedding_holds».«toFrac_prod_ne_zero» := P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_prod_ne_zero_82f3e7b02aa9
