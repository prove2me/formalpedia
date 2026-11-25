-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_gramC_append_blocks
-- name    : ReciprocityTheory.MultiplicativeHeights.DegAdd.gramC_append_blocks
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:37.058832+00:00
-- url     : https://prove2.me/theorems/2ddb804b-9066-5564-960c-f8a67e89f02c
-- title:
--   Deg Add: gram C append blocks
-- statement:
--   The Deg Add construction uses the gram C append blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/EmbMatMulVecInjective.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/EmbMatMulVecInjective.lean#L56-L61

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_EmbMatMulVecInjective
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
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open Matrix NumberField
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.DegAdd.gramC_append_blocks {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) :
    (gramC H σ (Fin.append b c)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (gramC H σ b) (gramX H σ b c) (gramX H σ c b) (gramC H σ c) := by sorry
