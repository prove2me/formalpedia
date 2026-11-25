-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotGram_det_pos
-- name    : ReciprocityTheory.ChartRestriction.G.T0.quotGram_det_pos
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:56.716881+00:00
-- url     : https://prove2.me/theorems/da5e0e2a-411c-4f4e-b6dd-a418ef04e983
-- title:
--   T0: quot Gram det pos
-- statement:
--   The T0 construction uses the quot Gram det pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L208-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L208-L236

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

theorem ReciprocityTheory.ChartRestriction.G.T0.quotGram_det_pos (σ : K →+* ℂ) {m : ℕ} {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) (hli : LinearIndependent K (Fin.append b c)) :
    0 < (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re := by sorry
