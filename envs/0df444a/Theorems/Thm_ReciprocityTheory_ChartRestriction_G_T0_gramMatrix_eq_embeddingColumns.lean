-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gramMatrix_eq_embeddingColumns
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gramMatrix_eq_embeddingColumns
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:58.411846+00:00
-- url     : https://prove2.me/theorems/fb1abc95-13ef-47e7-a2bd-86d702bf288e
-- title:
--   T0: gram Matrix eq embedding Columns
-- statement:
--   The T0 construction uses the gram Matrix eq embedding Columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L171-L175

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
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.gramMatrix_eq_embeddingColumns (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC 1 σ b = (hBm σ b)ᴴ * hBm σ b := by sorry
