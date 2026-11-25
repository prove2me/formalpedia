-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_BaseChangeC_isReduced_tensor_domain
-- name    : ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_domain
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:12.038969+00:00
-- url     : https://prove2.me/theorems/e40ed3cc-e394-48e1-99d1-6536bded092e
-- title:
--   Base Change C: is Reduced tensor domain
-- statement:
--   The Base Change C construction uses the is Reduced tensor domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCA.lean#L91-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeCA.lean#L91-L103

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

theorem ReciprocityTheory.AnForm.R.BaseChangeC.isReduced_tensor_domain (F K D : Type) [Field F] [Field K] [Algebra F K]
    [Algebra.FormallyUnramified F K] [Algebra.EssFiniteType F K] [CommRing D] [IsDomain D]
    [Algebra F D] : IsReduced (K ⊗[F] D) := by sorry
