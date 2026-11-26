-- Prove2me | Theorems.Thm_PsiReindexTilde
-- name    : PsiReindexTilde
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:28.284955+00:00
-- url     : https://prove2.me/theorems/bed43f95-e126-5da9-950d-2708dfcb6f6a
-- title:
--   Psi Reindex Tilde: Psi Reindex Tilde
-- statement:
--   The Psi Reindex Tilde construction uses the Psi Reindex Tilde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiReindexTilde.lean#L7-L108
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiReindexTilde.lean#L7-L108

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_curveRestrictTot
import Definitions.Def_Tablet_CurveRestrictTotAgrees
import Definitions.Def_Tablet_PsiReindex
import Definitions.Def_Tablet_PsiReindexTilde
import Theorems.Thm_CurveRestrictTotAgrees
import Theorems.Thm_PsiReindex

set_option autoImplicit false

theorem PsiReindexTilde {E : Type*} [MetricSpace E] (m l : ℕ) (hm : 0 < m) (hl : 0 < l)
    (Q : Finset E) (ε C : ℝ) (γ : Curve E) (hlen : γ.len = (l : ℝ)) :
    psiTilde (m * l) Q ε C γ
      = ∑ j ∈ Finset.Icc 1 l, psiTilde m Q ε C (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ)) := by sorry
