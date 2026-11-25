-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_fac_eq_zero_of_smul
-- name    : ReciprocityTheory.ChartRestriction.L1.fac_eq_zero_of_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:56.678077+00:00
-- url     : https://prove2.me/theorems/d1dfa554-f11b-4651-b4b6-445b0e59bbad
-- title:
--   L1: fac eq zero of smul
-- statement:
--   The L1 construction uses the fac eq zero of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModVanish.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModVanish.lean#L12-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModHnf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.fac_eq_zero_of_smul (t : ℕ × ℕ × ℕ) (τ : ℍ) (γ : SL(2, ℤ))
    (h : γ • pt t.1 t.2.1 t.2.2 τ = τ) : fac t τ = 0 := by sorry
