-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_spanIdx_ne_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.spanIdx_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:28.2108+00:00
-- url     : https://prove2.me/theorems/e30b85b3-eb3e-44b5-a0b5-02ff32e53b5f
-- title:
--   Semi Pt: span Idx ne zero
-- statement:
--   The Semi Pt construction uses the span Idx ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegE.lean#L56-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegE.lean#L56-L150

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.spanIdx_ne_zero {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (hB : B.FG)
    (hb : IsKBasisIn B b) : spanIdx B b ≠ 0 := by sorry
