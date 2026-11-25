-- Prove2me | Theorems.Thm_PI_EF_finite_zeros_of_compact
-- name    : PI.EF.finite_zeros_of_compact
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:41.009701+00:00
-- url     : https://prove2.me/theorems/9543beea-56a4-5db5-a575-aea7ce0c8296
-- title:
--   EF: finite zeros of compact
-- statement:
--   The EF construction uses the finite zeros of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructA.lean#L95-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructA.lean#L95-L109

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set

theorem PI.EF.finite_zeros_of_compact {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) : (K ∩ f ⁻¹' {0}).Finite := by sorry
