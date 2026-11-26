-- Prove2me | Theorems.Thm_PsiReindex
-- name    : PsiReindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:19.118846+00:00
-- url     : https://prove2.me/theorems/de9817e8-24bf-57d5-9035-42342c394196
-- title:
--   Psi Reindex: Psi Reindex
-- statement:
--   The Psi Reindex construction uses the Psi Reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiReindex.lean#L6-L120
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiReindex.lean#L6-L120

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_curveRestrictTot
import Definitions.Def_Tablet_CurveRestrictTotAgrees
import Definitions.Def_Tablet_PsiReindex
import Theorems.Thm_CurveRestrictTotAgrees

set_option autoImplicit false

theorem PsiReindex {E : Type*} [MetricSpace E] (m l : ℕ) (hm : 0 < m) (hl : 0 < l)
    (Q : Finset E) (ε C : ℝ) (γ : Curve E) (hlen : γ.len = (l : ℝ)) :
    psi (m * l) Q ε C γ
      = ∑ j ∈ Finset.Icc 1 l, psi m Q ε C (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ)) := by sorry
