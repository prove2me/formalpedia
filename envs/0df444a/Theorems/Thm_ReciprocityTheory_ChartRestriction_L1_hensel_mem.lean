-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hensel_mem
-- name    : ReciprocityTheory.ChartRestriction.L1.hensel_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:59.411732+00:00
-- url     : https://prove2.me/theorems/44bc2024-9c96-4577-8e5d-a53eb50790b3
-- title:
--   L1: hensel mem
-- statement:
--   The L1 construction uses the hensel mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorHensel.lean#L16-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorHensel.lean#L16-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurNewton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.hensel_mem (P : Polynomial ℂ_[l]) (hK : ∀ i, P.coeff i ∈ MaximalUnramifiedExtension l) (hP : ∀ i, ‖P.coeff i‖ ≤ 1)
    (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (h0 : P.eval x = 0) (h1 : ‖P.derivative.eval x‖ = 1) : x ∈ MaximalUnramifiedExtension l := by sorry
