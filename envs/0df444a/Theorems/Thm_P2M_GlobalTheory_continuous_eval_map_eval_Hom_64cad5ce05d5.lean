-- Prove2me | Theorems.Thm_P2M_GlobalTheory_continuous_eval_map_eval_Hom_64cad5ce05d5
-- name    : P2M_GlobalTheory_continuous_eval_map_eval_Hom_64cad5ce05d5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:53.528338+00:00
-- url     : https://prove2.me/theorems/9fa5c5e0-89fe-4a2a-9b4b-0e24455e7a3c
-- title:
--   P2 M Global Theory continuous eval map eval Hom 64cad5ce05d5: P2 M Global Theory continuous eval map eval Hom 64cad5ce05d5
-- statement:
--   The P2 M Global Theory continuous eval map eval Hom 64cad5ce05d5 construction uses the P2 M Global Theory continuous eval map eval Hom 64cad5ce05d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsEmbeddingsOverInjective.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsEmbeddingsOverInjective.lean#L136-L142

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory

theorem P2M_GlobalTheory_continuous_eval_map_eval_Hom_64cad5ce05d5 {K : Type*} [CommRing K] (sg : K →+* ℂ) {D : ℕ}
    (μ : Polynomial (MvPolynomial (Fin D) K)) (x : ℂ) :
    Continuous fun z : Fin D → ℂ => (μ.map (MvPolynomial.eval₂Hom sg z)).eval x := by sorry

alias «GlobalTheory».«continuous_eval_map_eval₂Hom» := P2M_GlobalTheory_continuous_eval_map_eval_Hom_64cad5ce05d5
