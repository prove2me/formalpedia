-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_re_mdisc_cons_conjTranspose
-- name    : ReciprocityTheory.AnForm.A.re_mdisc_cons_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:34.756934+00:00
-- url     : https://prove2.me/theorems/200b72a5-55af-4a13-a30b-e95065207dfe
-- title:
--   A: re mdisc cons conj Transpose
-- statement:
--   The A construction uses the re mdisc cons conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsAlg.lean#L129-L140

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

theorem ReciprocityTheory.AnForm.A.re_mdisc_cons_conjTranspose (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hB : ∀ i, (B i).IsHermitian) :
    (mdisc (Fin.cons Aᴴ B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re =
      (mdisc (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).re := by sorry
