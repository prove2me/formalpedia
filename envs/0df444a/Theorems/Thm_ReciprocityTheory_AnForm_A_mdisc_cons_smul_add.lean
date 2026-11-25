-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_add
-- name    : ReciprocityTheory.AnForm.A.mdisc_cons_smul_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:47.692252+00:00
-- url     : https://prove2.me/theorems/78431f89-6935-4a32-a110-5b6b1fff306c
-- title:
--   A: mdisc cons smul add
-- statement:
--   The A construction uses the mdisc cons smul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L142-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L142-L153

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.mdisc_cons_smul_add (c c' : ℂ) (A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons (c • A + c' • A') B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      c * mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) +
        c' * mdisc (Fin.cons A' B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by sorry
