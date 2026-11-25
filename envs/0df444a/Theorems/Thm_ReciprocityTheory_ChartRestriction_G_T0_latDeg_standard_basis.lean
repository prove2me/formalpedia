-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_latDeg_standard_basis
-- name    : ReciprocityTheory.ChartRestriction.G.T0.latDeg_standard_basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:11.461776+00:00
-- url     : https://prove2.me/theorems/2d445018-7a6b-425e-85e4-e4764f6a3853
-- title:
--   T0: lat Deg standard basis
-- statement:
--   The T0 construction uses the lat Deg standard basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L135-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L135-L180

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

theorem ReciprocityTheory.ChartRestriction.G.T0.latDeg_standard_basis {n : ℕ} (h : n = r) (v : Fin n → Fin r → K)
    (hv : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn (hStd K r) v) :
    ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) v = 0 := by sorry
