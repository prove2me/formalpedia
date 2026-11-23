-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_norm_one_mul_mem
-- name    : ReciprocityTheory.ChartRestriction.L3.WA.exists_norm_one_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:27.117173+00:00
-- url     : https://prove2.me/theorems/fb004dd8-a736-4ef3-8b0a-47cffbf49898
-- title:
--   WA: exists norm one mul mem
-- statement:
--   The WA construction uses the exists norm one mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsNormOneOfPair.lean#L37-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/HermitianGenusExtension/SemilocalHermitianLattices/ExistsNormOneOfPair.lean#L37-L80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K}

theorem ReciprocityTheory.ChartRestriction.L3.WA.exists_norm_one_mul_mem (hS : IsHermSemilocal S) {a : K} (ha : star a * a ∈ S) :
    ∃ b : K, star b * b = 1 ∧ a * b ∈ S := by sorry
