-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_polMap
-- name    : ReciprocityTheory.ChartRestriction.L1.coeff_polMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:10.130129+00:00
-- url     : https://prove2.me/theorems/ffaf869d-55f1-4fb4-9349-ad23cbbdcebd
-- title:
--   L1: coeff pol Map
-- statement:
--   The L1 construction uses the coeff pol Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProj.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProj.lean#L29-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {E : Type} [Field E]

theorem ReciprocityTheory.ChartRestriction.L1.coeff_polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) (i : ℕ) :
    (polMap ψ m Q).coeff i = if i ≤ m then ψ (Q.coeff i) else 0 := by sorry
