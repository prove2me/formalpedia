-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_finite_place_add_eq_of_lt
-- name    : ReciprocityTheory.MultiplicativeHeights.finite_place_add_eq_of_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:28.826728+00:00
-- url     : https://prove2.me/theorems/0c7ba49e-4715-40af-8914-5c124fee48a2
-- title:
--   Multiplicative Heights: finite place add eq of lt
-- statement:
--   The Multiplicative Heights construction uses the finite place add eq of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GaussAbsMulOfMonomialOrder.lean#L58-L67

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem ReciprocityTheory.MultiplicativeHeights.finite_place_add_eq_of_lt (w : FinitePlace K) (x y : K) (h : w y < w x) : w (x + y) = w x := by sorry
