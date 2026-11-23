-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_P_cf_cpP
-- name    : ReciprocityTheory.AnForm.P.cf_cpP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:51.103721+00:00
-- url     : https://prove2.me/theorems/86b0f267-6616-4feb-abf0-c983585e019c
-- title:
--   P: cf cp P
-- statement:
--   The P construction uses the cf cp P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean#L88-L94

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

theorem ReciprocityTheory.AnForm.P.cf_cpP (N n : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) :
    cf n (cpP N A) = if n < N then ((n.factorial : ℂ)⁻¹) • A ^ n else 0 := by sorry
