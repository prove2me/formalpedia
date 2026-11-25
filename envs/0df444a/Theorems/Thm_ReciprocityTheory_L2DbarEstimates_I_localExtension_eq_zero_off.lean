-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_localExtension_eq_zero_off
-- name    : ReciprocityTheory.L2DbarEstimates.I.localExtension_eq_zero_off
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:59:06.714624+00:00
-- url     : https://prove2.me/theorems/9097ac6e-f706-4937-8fd1-83ec142368d1
-- title:
--   I: local Extension eq zero off
-- statement:
--   The I construction uses the local Extension eq zero off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/LocalExtensionEqMulJacobian.lean#L63-L67

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.localExtension_eq_zero_off {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (c : M → ℂ) (W : M → Set M) {x : M}
    (hx : ∀ p ∈ zeroSet n g, x ∉ W p) : gt n z g c W x = 0 := by sorry
