-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotientGram_det_re_eq
-- name    : ReciprocityTheory.ChartRestriction.G.T0.quotientGram_det_re_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:22.708329+00:00
-- url     : https://prove2.me/theorems/f5134ecb-2fef-4f64-a8b1-9dd0ce7e771a
-- title:
--   T0: quotient Gram det re eq
-- statement:
--   The T0 construction uses the quotient Gram det re eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulVecConjugate.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OrthogonalProjectorMulVecConjugate.lean#L65-L71

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

theorem ReciprocityTheory.ChartRestriction.G.T0.quotientGram_det_re_eq (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ) = (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det := by sorry
