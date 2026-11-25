-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_mulVec_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_mulVec_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:42.195568+00:00
-- url     : https://prove2.me/theorems/406aab1f-c5a6-5199-838d-f9d2e559d204
-- title:
--   T0: orthogonal Projector mul Vec eq zero
-- statement:
--   The T0 construction uses the orthogonal Projector mul Vec eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L149-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L149-L157

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
variable {K : Type} [Field K] {r k : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_mulVec_eq_zero (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {q : Fin r → K} (hq : q ∈ Submodule.span K (Set.range b)) :
    hPm σ b *ᵥ (fun i => σ (q i)) = 0 := by sorry
