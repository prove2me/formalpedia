-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_conjugate
-- name    : ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_conjugate
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:03.299521+00:00
-- url     : https://prove2.me/theorems/ac828646-1017-4512-90c6-8a2640d3397d
-- title:
--   T0: orthogonal Projector conjugate
-- statement:
--   The T0 construction uses the orthogonal Projector conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulVecConjugate.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulVecConjugate.lean#L25-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
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
open scoped ComplexOrder Kronecker
variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_conjugate (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm (conjugate σ) b = (hPm σ b).map (starRingEnd ℂ) := by sorry
