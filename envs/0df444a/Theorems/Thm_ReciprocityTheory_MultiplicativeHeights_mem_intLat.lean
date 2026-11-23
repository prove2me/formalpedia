-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_mem_intLat
-- name    : ReciprocityTheory.MultiplicativeHeights.mem_intLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:45.263002+00:00
-- url     : https://prove2.me/theorems/17d0373c-6ae0-4228-948f-e4d14db7b54c
-- title:
--   Multiplicative Heights: mem int Lat
-- statement:
--   The Multiplicative Heights construction uses the mem int Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LatTest.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LatTest.lean#L109-L112

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.mem_intLat {K : Type} [Field K] [NumberField K] {r : ℕ} (x : Fin r → K) :
    x ∈ intLat K r ↔ ∀ a, IsIntegralElt (x a) := by sorry
