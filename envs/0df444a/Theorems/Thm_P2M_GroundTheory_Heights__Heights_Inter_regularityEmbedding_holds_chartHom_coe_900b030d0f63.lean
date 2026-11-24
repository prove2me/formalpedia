-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_coe_900b030d0f63
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_coe_900b030d0f63
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:50.999928+00:00
-- url     : https://prove2.me/theorems/7540b9de-8d63-4581-a3bc-cc27106a5012
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart Hom coe 900b030d0f63: P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart Hom coe 900b030d0f63
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart Hom coe 900b030d0f63 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart Hom coe 900b030d0f63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L121-L127

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

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_coe_900b030d0f63 {P : Ideal (MRing ι)} (r : (Σ k, ι k) → funField P) (f : MRing ι) :
    (chartHom r f : FractionRing (MRing ι ⧸ P)) =
      eval₂Hom (Int.castRingHom _) (fun p => (r p : FractionRing (MRing ι ⧸ P))) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityEmbedding_holds».«chartHom_coe» := P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_coe_900b030d0f63
