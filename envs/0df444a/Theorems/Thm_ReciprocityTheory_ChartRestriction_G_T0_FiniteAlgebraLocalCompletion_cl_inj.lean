-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_inj
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:22.511803+00:00
-- url     : https://prove2.me/theorems/1ba16865-6ea2-4340-8fb0-750409ee0f66
-- title:
--   Finite Algebra Local Completion: cl inj
-- statement:
--   The Finite Algebra Local Completion construction uses the cl inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L186-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean#L186-L189

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
  (L : Type*) [Field L] [Algebra R L] [FaithfulSMul R L] [Module.Finite R (integralClosure R L)]

theorem ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj : Function.Injective (algebraMap R (integralClosure R L)) := by sorry
