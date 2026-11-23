-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_pi_single_one_mem_hStd
-- name    : ReciprocityTheory.ChartRestriction.G.T0.pi_single_one_mem_hStd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:28.654844+00:00
-- url     : https://prove2.me/theorems/230c4d87-7011-4e6c-946d-b1be470d8a11
-- title:
--   T0: pi single one mem h Std
-- statement:
--   The T0 construction uses the pi single one mem h Std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L21-L26

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

theorem ReciprocityTheory.ChartRestriction.G.T0.pi_single_one_mem_hStd (i : Fin r) : (Pi.single i (1 : K) : Fin r → K) ∈ hStd K r := by sorry
