-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_faithful
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:27.378963+00:00
-- url     : https://prove2.me/theorems/a8f79404-77e6-4207-b7bd-c1fbd1ab0f15
-- title:
--   Finite Algebra Local Completion: cl faithful
-- statement:
--   The Finite Algebra Local Completion construction uses the cl faithful property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L208-L211

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
open IsLocalRing Polynomial
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
include K

theorem ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful : FaithfulSMul R L := by sorry
