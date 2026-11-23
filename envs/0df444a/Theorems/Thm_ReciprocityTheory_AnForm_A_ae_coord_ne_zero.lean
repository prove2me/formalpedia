-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_ae_coord_ne_zero
-- name    : ReciprocityTheory.AnForm.A.ae_coord_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:28.379196+00:00
-- url     : https://prove2.me/theorems/5129abd9-eceb-4be6-9a80-cca72aeb334a
-- title:
--   A: ae coord ne zero
-- statement:
--   The A construction uses the ae coord ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L141-L145

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.A.ae_coord_ne_zero {n : ℕ} (i : Fin (n + 1)) : ∀ᵐ z : Fin (n + 1) → ℂ ∂volume, z i ≠ 0 := by sorry
