-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_absNorm_span
-- name    : ReciprocityTheory.ChartRestriction.L1.absNorm_span
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:45.661157+00:00
-- url     : https://prove2.me/theorems/342b88b0-d110-588d-9bf8-b8eb393be773
-- title:
--   L1: abs Norm span
-- statement:
--   The L1 construction uses the abs Norm span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModPrincNorm.lean#L64-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModPrincNorm.lean#L64-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQuadInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPrincNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.absNorm_span {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (x : 𝓞 (KQ d)) (a b : ℤ)
    (h : (((x : KQ d) : ℂ)) = a + b * omegaK d) :
    4 * (Ideal.absNorm (Ideal.span {x}) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by sorry
