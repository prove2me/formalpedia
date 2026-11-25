-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotGram_eq_conjTranspose_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.quotGram_eq_conjTranspose_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:28.344644+00:00
-- url     : https://prove2.me/theorems/ff44286e-03a6-52f1-acbb-1680b4abf201
-- title:
--   T0: quot Gram eq conj Transpose mul
-- statement:
--   The T0 construction uses the quot Gram eq conj Transpose mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L198-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L198-L206

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.quotGram_eq_conjTranspose_mul (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {m : ℕ} (c : Fin m → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hPm σ b * hBm σ c)ᴴ * (hPm σ b * hBm σ c) := by sorry
