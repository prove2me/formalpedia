-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_linearIndependent_map_embedding
-- name    : ReciprocityTheory.ChartRestriction.G.T0.linearIndependent_map_embedding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:53.62812+00:00
-- url     : https://prove2.me/theorems/4611022c-5470-468e-9f40-c77e4e2a3197
-- title:
--   T0: linear Independent map embedding
-- statement:
--   The T0 construction uses the linear Independent map embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulEmbeddingColumns.lean#L56-L61

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

theorem ReciprocityTheory.ChartRestriction.G.T0.linearIndependent_map_embedding (σ : K →+* ℂ) {ι : Type*} {v : ι → Fin r → K}
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => fun l => σ (v i l)) := by sorry
