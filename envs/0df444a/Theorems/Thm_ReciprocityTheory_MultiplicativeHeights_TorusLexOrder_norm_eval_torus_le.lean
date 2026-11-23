-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_norm_eval_torus_le
-- name    : ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.norm_eval_torus_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:06.126701+00:00
-- url     : https://prove2.me/theorems/c77addd7-5caa-42e0-97ef-f02c776aac0f
-- title:
--   Torus Lex Order: norm eval torus le
-- statement:
--   The Torus Lex Order construction uses the norm eval torus le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexB.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexB.lean#L87-L92

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate

theorem ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.norm_eval_torus_le {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    ‖MvPolynomial.eval (torusPoint θ) f‖ ≤ ∑ s ∈ f.support, ‖f.coeff s‖ := by sorry
