-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_mul_low
-- name    : ReciprocityTheory.ChartRestriction.L1.coeff_mul_low
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:37.131954+00:00
-- url     : https://prove2.me/theorems/2ce6dc34-5ffb-483d-aa15-164293252d7d
-- title:
--   L1: coeff mul low
-- statement:
--   The L1 construction uses the coeff mul low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModQPrin.lean#L44-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModQPrin.lean#L44-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
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

theorem ReciprocityTheory.ChartRestriction.L1.coeff_mul_low (V G : PowerSeries ℂ) (hV : PowerSeries.coeff 0 V = 1) (n : ℕ)
    (hG : ∀ i < n, PowerSeries.coeff i G = 0) :
    (∀ i < n, PowerSeries.coeff i (V * G) = 0) ∧
      PowerSeries.coeff n (V * G) = PowerSeries.coeff n G := by sorry
