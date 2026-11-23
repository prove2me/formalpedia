-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul
-- name    : ReciprocityTheory.AnForm.P.cf_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:48.081163+00:00
-- url     : https://prove2.me/theorems/b9584231-30bc-4ee8-973a-60d4ff229e1e
-- title:
--   P: cf mul
-- statement:
--   The P construction uses the cf mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensA.lean#L95-L100

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.P.cf_mul {α β γ : Type*} [Fintype β] (n : ℕ) (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf n (P * Q) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, cf x.1 P * cf x.2 Q := by sorry
