-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_smul_right
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_jForm_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:45.095801+00:00
-- url     : https://prove2.me/theorems/d26c107d-4fd8-4697-902b-548bf2839d68
-- title:
--   Multiplicative Heights: approx B j Form smul right
-- statement:
--   The Multiplicative Heights construction uses the approx B j Form smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L14-L17

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.approxB_jForm_smul_right (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) (a : ℂ) :
    jForm p x (a • y) = a * jForm p x y := by sorry
