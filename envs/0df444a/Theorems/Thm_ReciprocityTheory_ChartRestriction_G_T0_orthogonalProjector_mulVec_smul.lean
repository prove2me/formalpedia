-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_mulVec_smul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_mulVec_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:54.574706+00:00
-- url     : https://prove2.me/theorems/64425705-f331-4734-af5c-7cfb2eac3022
-- title:
--   T0: orthogonal Projector mul Vec smul
-- statement:
--   The T0 construction uses the orthogonal Projector mul Vec smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulVecSmul.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulVecSmul.lean#L102-L107

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

theorem ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_mulVec_smul (σ : K →+* ℂ) (b : Fin k → Fin r → K) (a : K) (x : Fin r → K) :
    (hPm σ b *ᵥ fun l => σ ((a • x) l)) = σ a • (hPm σ b *ᵥ fun l => σ (x l)) := by sorry
