-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_mul_d94a61c7c2a6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_mul_d94a61c7c2a6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:27.336971+00:00
-- url     : https://prove2.me/theorems/e1aa67a6-f96a-4fad-ba52-53b5c49a1de2
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart Hom mul d94a61c7c2a6: P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart Hom mul d94a61c7c2a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart Hom mul d94a61c7c2a6 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart Hom mul d94a61c7c2a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L141-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L141-L164

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_mul_d94a61c7c2a6 {P : Ideal (MRing ι)} (j : ∀ k, ι k) (r : (Σ k, ι k) → funField P)
    (hr : ∀ p : Σ k, ι k, (r p : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, j p.1⟩) = toFrac P (X p))
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    (chartHom r f : FractionRing (MRing ι ⧸ P)) * toFrac P (∏ k, (X ⟨k, j k⟩ : MRing ι) ^ a k) = toFrac P f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityEmbedding_holds».«chartHom_mul» := P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_mul_d94a61c7c2a6
