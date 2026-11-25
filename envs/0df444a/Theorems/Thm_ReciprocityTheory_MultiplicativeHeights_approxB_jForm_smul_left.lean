-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_smul_left
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_jForm_smul_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:05.317909+00:00
-- url     : https://prove2.me/theorems/b26552bc-93ea-47ba-8aa8-19997444744f
-- title:
--   Multiplicative Heights: approx B j Form smul left
-- statement:
--   The Multiplicative Heights construction uses the approx B j Form smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L28-L31

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

theorem ReciprocityTheory.MultiplicativeHeights.approxB_jForm_smul_left (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) (a : ℂ) :
    jForm p (a • x) y = conj a * jForm p x y := by sorry
