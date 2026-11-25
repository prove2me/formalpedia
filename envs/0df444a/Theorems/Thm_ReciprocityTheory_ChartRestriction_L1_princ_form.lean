-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_princ_form
-- name    : ReciprocityTheory.ChartRestriction.L1.princ_form
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:44.607391+00:00
-- url     : https://prove2.me/theorems/52f07301-11fe-5ab4-89e9-53328d7898bb
-- title:
--   L1: princ form
-- statement:
--   The L1 construction uses the princ form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModPrincNorm.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModPrincNorm.lean#L83-L90

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

theorem ReciprocityTheory.ChartRestriction.L1.princ_form {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (v : HeightOneSpectrum (𝓞 (KQ d)))
    (hv : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1) :
    ∃ a b : ℤ, 4 * (Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by sorry
