-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_cf_mul_zero
-- name    : ReciprocityTheory.AnForm.P.cf_mul_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:35.702904+00:00
-- url     : https://prove2.me/theorems/aa69d1d6-3bda-4c8e-af03-2eb4fafa0064
-- title:
--   P: cf mul zero
-- statement:
--   The P construction uses the cf mul zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L9-L12

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.P.cf_mul_zero {α β γ : Type*} [Fintype β] (P : Matrix α β ℂ[X]) (Q : Matrix β γ ℂ[X]) :
    cf 0 (P * Q) = cf 0 P * cf 0 Q := by sorry
