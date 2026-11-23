-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gramC_eq_colMat
-- name    : ReciprocityTheory.MultiplicativeHeights.gramC_eq_colMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:18.834531+00:00
-- url     : https://prove2.me/theorems/c9177433-033d-4d0d-ae25-286bf64d04fa
-- title:
--   Multiplicative Heights: gram C eq col Mat
-- statement:
--   The Multiplicative Heights construction uses the gram C eq col Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L14-L22

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
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

theorem ReciprocityTheory.MultiplicativeHeights.gramC_eq_colMat {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (colMat σ b)ᴴ * H * colMat σ b := by sorry
