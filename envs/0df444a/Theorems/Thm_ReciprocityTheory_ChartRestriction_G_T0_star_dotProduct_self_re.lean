-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_star_dotProduct_self_re
-- name    : ReciprocityTheory.ChartRestriction.G.T0.star_dotProduct_self_re
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:36.187418+00:00
-- url     : https://prove2.me/theorems/70b3bf5a-a61d-54d1-8330-89fa2d06ecfa
-- title:
--   T0: star dot Product self re
-- statement:
--   The T0 construction uses the star dot Product self re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulVecSmul.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulVecSmul.lean#L34-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.star_dotProduct_self_re {r : ℕ} (v : Fin r → ℂ) : (star v ⬝ᵥ v).re = hns v := by sorry
