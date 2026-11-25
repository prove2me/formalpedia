-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_re_mdisc_cons_vecMulVec_nonneg
-- name    : ReciprocityTheory.AnForm.A.re_mdisc_cons_vecMulVec_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:35.890124+00:00
-- url     : https://prove2.me/theorems/afe8e938-8ecc-45ca-9ad9-6592cd2f0c61
-- title:
--   A: re mdisc cons vec Mul Vec nonneg
-- statement:
--   The A construction uses the re mdisc cons vec Mul Vec nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L162-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L162-L169

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

theorem ReciprocityTheory.AnForm.A.re_mdisc_cons_vecMulVec_nonneg (a : Fin (n + 1) → ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : ∀ i, (B i).PosSemidef) :
    0 ≤ (mdisc (Fin.cons (vecMulVec a (star a)) B :
      Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re := by sorry
