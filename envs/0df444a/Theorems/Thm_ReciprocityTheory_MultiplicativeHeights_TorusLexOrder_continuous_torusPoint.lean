-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_continuous_torusPoint
-- name    : ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.continuous_torusPoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:42.993228+00:00
-- url     : https://prove2.me/theorems/84a0d87e-b3d0-4cdf-80e0-179299aac37a
-- title:
--   Torus Lex Order: continuous torus Point
-- statement:
--   The Torus Lex Order construction uses the continuous torus Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexB.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusLexB.lean#L52-L53

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

theorem ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.continuous_torusPoint {ι : Type} : Continuous (fun θ : ι → ℝ => torusPoint θ) := by sorry
