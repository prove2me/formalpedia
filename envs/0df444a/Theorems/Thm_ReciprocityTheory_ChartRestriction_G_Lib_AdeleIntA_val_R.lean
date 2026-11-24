-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lib_AdeleIntA_val_R
-- name    : ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.val_R
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:32.825041+00:00
-- url     : https://prove2.me/theorems/18841002-0f09-4556-9e5f-510883b571c1
-- title:
--   Adele Int A: val R
-- statement:
--   The Adele Int A construction uses the val R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/AdeleApproximation/AdeleIntA.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/AdeleApproximation/AdeleIntA.lean#L29-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lib ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.val_R (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by sorry
