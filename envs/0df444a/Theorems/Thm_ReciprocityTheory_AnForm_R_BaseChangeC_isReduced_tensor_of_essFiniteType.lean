-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isReduced_tensor_of_essFiniteType
-- name    : ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:53.82988+00:00
-- url     : https://prove2.me/theorems/54c9daec-ed81-4089-81b9-07bc556dd021
-- title:
--   Base Change C: is Reduced tensor of ess Finite Type
-- statement:
--   The Base Change C construction uses the is Reduced tensor of ess Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCA.lean#L105-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCA.lean#L105-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
attribute [-instance] DivisionRing.toRatAlgebra

theorem ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_of_essFiniteType (K : Type) [Field K] [Algebra ℚ K]
    [Algebra.EssFiniteType ℚ K] (C : Type) [Field C] [Algebra ℚ C] : IsReduced (K ⊗[ℚ] C) := by sorry
