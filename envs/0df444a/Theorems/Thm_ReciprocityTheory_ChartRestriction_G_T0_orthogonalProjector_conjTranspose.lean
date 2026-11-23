-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_conjTranspose
-- name    : ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:41.550867+00:00
-- url     : https://prove2.me/theorems/07057940-8881-461d-a2eb-0ef24b0d8d4f
-- title:
--   T0: orthogonal Projector conj Transpose
-- statement:
--   The T0 construction uses the orthogonal Projector conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L98-L100

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

theorem ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_conjTranspose (σ : K →+* ℂ) (b : Fin k → Fin r → K) : (hPm σ b)ᴴ = hPm σ b := by sorry
