-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_norm_weierstrass_coeff_small_j
-- name    : ReciprocityTheory.ChartRestriction.L1.norm_weierstrass_coeff_small_j
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:07:59.064798+00:00
-- url     : https://prove2.me/theorems/24db9e13-8496-53a1-aac8-3591b8793ea3
-- title:
--   L1: norm weierstrass coeff small j
-- statement:
--   The L1 construction uses the norm weierstrass coeff small j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormWeierstrassCoeffSmallJ.lean#L76-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormWeierstrassCoeffSmallJ.lean#L76-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedValB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKurOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_G2EqZeroOfHasCMByThree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormWeierstrassCoeffSmallJ
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
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.norm_weierstrass_coeff_small_j (h5 : 5 ≤ l) {J : ℂ_[l]} (hJ : ‖J‖ < 1) :
    ‖27 * J / (J - 1728)‖ = ‖J‖ ∧
      ‖(27 * J / (J - 1728)) ^ 3 - 27 * (27 * J / (J - 1728)) ^ 2‖ = ‖J‖ ^ 2 := by sorry
