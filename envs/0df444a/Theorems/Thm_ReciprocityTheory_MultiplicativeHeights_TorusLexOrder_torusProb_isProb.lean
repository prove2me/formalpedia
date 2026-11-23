-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torusProb_isProb
-- name    : ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.torusProb_isProb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:00.903675+00:00
-- url     : https://prove2.me/theorems/2e95cc1d-db8f-4017-a4c5-05fcffa75e30
-- title:
--   Torus Lex Order: torus Prob is Prob
-- statement:
--   The Torus Lex Order construction uses the torus Prob is Prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexB.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexB.lean#L7-L10

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

theorem ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.torusProb_isProb (ι : Type) [Fintype ι] : IsProbabilityMeasure (torusProb ι) := by sorry
