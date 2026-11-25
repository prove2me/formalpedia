-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_harmonic_pred_le_one_add_log
-- name    : ReciprocityTheory.MultiplicativeHeights.harmonic_pred_le_one_add_log
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:04.546008+00:00
-- url     : https://prove2.me/theorems/62c8f123-8a18-4331-98b7-88c16ddffefa
-- title:
--   Multiplicative Heights: harmonic pred le one add log
-- statement:
--   The Multiplicative Heights construction uses the harmonic pred le one add log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LogNormCoeffSubLeBlockSphereLogMean.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LogNormCoeffSubLeBlockSphereLogMean.lean#L9-L18

import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormCoeffSubLeBlockSphereLogMean
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
open MeasureTheory MvPolynomial NumberField

theorem ReciprocityTheory.MultiplicativeHeights.harmonic_pred_le_one_add_log {n : ℕ} (hn : 0 < n) : (harmonic (n - 1) : ℝ) ≤ 1 + Real.log n := by sorry
