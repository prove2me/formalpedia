-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IsotropicCombinations_herm_sum_smul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.herm_sum_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:49.176046+00:00
-- url     : https://prove2.me/theorems/f93c7fe5-eb3f-5b33-a2d0-5eb563b7b500
-- title:
--   Isotropic Combinations: herm sum smul
-- statement:
--   The Isotropic Combinations construction uses the herm sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/IsotropicCombinations.lean#L23-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicIndexSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCombinations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {n : ℕ} (G : Matrix (Fin r) (Fin r) E)

theorem ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations.herm_sum_smul (c : Fin n → E) (β : Fin n → Fin r → E) (y : Fin r → E) :
    herm G (∑ k, c k • β k) y = ∑ k, c k * herm G (β k) y := by sorry
