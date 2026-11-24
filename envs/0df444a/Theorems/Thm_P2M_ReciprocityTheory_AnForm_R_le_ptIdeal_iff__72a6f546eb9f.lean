-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_le_ptIdeal_iff__72a6f546eb9f
-- name    : P2M_ReciprocityTheory_AnForm_R_le_ptIdeal_iff__72a6f546eb9f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:48.271329+00:00
-- url     : https://prove2.me/theorems/f05352f4-d378-474b-8a85-485a8b4c215c
-- title:
--   P2 M Reciprocity Theory An Form R le pt Ideal iff  72a6f546eb9f: P2 M Reciprocity Theory An Form R le pt Ideal iff  72a6f546eb9f
-- statement:
--   The P2 M Reciprocity Theory An Form R le pt Ideal iff  72a6f546eb9f construction uses the P2 M Reciprocity Theory An Form R le pt Ideal iff  72a6f546eb9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocA.lean#L62-L64

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

theorem P2M_ReciprocityTheory_AnForm_R_le_ptIdeal_iff__72a6f546eb9f (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    K ≤ ptIdeal p ↔ ∀ h ∈ K, eval p h = 0 := by sorry

alias «ReciprocityTheory».«AnForm».«R».«le_ptIdeal_iff'» := P2M_ReciprocityTheory_AnForm_R_le_ptIdeal_iff__72a6f546eb9f
