-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_mk_mem_ptQ
-- name    : ReciprocityTheory.AnForm.R.mk_mem_ptQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:02.775709+00:00
-- url     : https://prove2.me/theorems/b4148d08-d17b-4ae7-9971-23f7c408a763
-- title:
--   R: mk mem pt Q
-- statement:
--   The R construction uses the mk mem pt Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L13-L15

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.mk_mem_ptQ {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ} (hK : K ≤ ptIdeal p)
    (f : MvPolynomial (Fin n) ℂ) : Ideal.Quotient.mk K f ∈ ptQ K p ↔ f ∈ ptIdeal p := by sorry
