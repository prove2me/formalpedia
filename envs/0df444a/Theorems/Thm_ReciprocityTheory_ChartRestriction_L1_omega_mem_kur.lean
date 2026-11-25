-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_omega_mem_kur
-- name    : ReciprocityTheory.ChartRestriction.L1.omega_mem_kur
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:33:06.053111+00:00
-- url     : https://prove2.me/theorems/4b3b9818-eda0-52d0-9935-7f45202164f0
-- title:
--   L1: omega mem kur
-- statement:
--   The L1 construction uses the omega mem kur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKurOmega.lean#L24-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKurOmega.lean#L24-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorHensel
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKurOmega
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

theorem ReciprocityTheory.ChartRestriction.L1.omega_mem_kur (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (l : ℕ) [Fact l.Prime] (hld : ¬ l ∣ d)
    (ι : ℂ ≃+* ℂ_[l]) : ι (omegaK d) ∈ MaximalUnramifiedExtension l := by sorry
