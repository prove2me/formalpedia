-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_normSqSum_add_of_orthogonal
-- name    : ReciprocityTheory.ChartRestriction.G.T0.normSqSum_add_of_orthogonal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:28.411888+00:00
-- url     : https://prove2.me/theorems/ef614ef0-d3fa-5613-b190-418584069ff8
-- title:
--   T0: norm Sq Sum add of orthogonal
-- statement:
--   The T0 construction uses the norm Sq Sum add of orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L116-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L116-L124

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

theorem ReciprocityTheory.ChartRestriction.G.T0.normSqSum_add_of_orthogonal {r : ℕ} (a c : Fin r → ℂ) (h : star a ⬝ᵥ c = 0) :
    hns (a + c) = hns a + hns c := by sorry
