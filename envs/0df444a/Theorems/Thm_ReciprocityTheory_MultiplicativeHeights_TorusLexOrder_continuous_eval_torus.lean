-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_continuous_eval_torus
-- name    : ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.continuous_eval_torus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:53.683954+00:00
-- url     : https://prove2.me/theorems/e333c2fa-90e3-4f48-9597-b6aeceb8b39d
-- title:
--   Torus Lex Order: continuous eval torus
-- statement:
--   The Torus Lex Order construction uses the continuous eval torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexB.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexB.lean#L94-L96

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

theorem ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.continuous_eval_torus {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    Continuous (fun θ : ι → ℝ => MvPolynomial.eval (torusPoint θ) f) := by sorry
