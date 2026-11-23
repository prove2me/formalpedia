-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hStd_eq_span_pi_single
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hStd_eq_span_pi_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:36.437094+00:00
-- url     : https://prove2.me/theorems/7907b505-cf50-4f82-9027-21db209b0001
-- title:
--   T0: h Std eq span pi single
-- statement:
--   The T0 construction uses the h Std eq span pi single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L28-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SingleMemStandardLattice.lean#L28-L45

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

theorem ReciprocityTheory.ChartRestriction.G.T0.hStd_eq_span_pi_single : hStd K r =
    Submodule.span (𝓞 K) (Set.range fun i : Fin r => (Pi.single i (1 : K) : Fin r → K)) := by sorry
