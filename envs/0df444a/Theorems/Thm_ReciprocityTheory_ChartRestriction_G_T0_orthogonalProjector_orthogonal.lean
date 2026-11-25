-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_orthogonal
-- name    : ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_orthogonal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:52.879602+00:00
-- url     : https://prove2.me/theorems/2a5e6724-7861-430a-a5ed-edfbc2860191
-- title:
--   T0: orthogonal Projector orthogonal
-- statement:
--   The T0 construction uses the orthogonal Projector orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L111-L114

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

theorem ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_orthogonal (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (v : Fin r → ℂ) (y : Fin k → ℂ) : star (hPm σ b *ᵥ v) ⬝ᵥ (hBm σ b *ᵥ y) = 0 := by sorry
