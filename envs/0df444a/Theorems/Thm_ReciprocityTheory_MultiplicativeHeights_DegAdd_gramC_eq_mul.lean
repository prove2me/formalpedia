-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_gramC_eq_mul
-- name    : ReciprocityTheory.MultiplicativeHeights.DegAdd.gramC_eq_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:42.69758+00:00
-- url     : https://prove2.me/theorems/e2b9221e-9d8b-469c-8317-60bb7950f28c
-- title:
--   Deg Add: gram C eq mul
-- statement:
--   The Deg Add construction uses the gram C eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/EmbMatMulVecInjective.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/EmbMatMulVecInjective.lean#L16-L24

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

theorem ReciprocityTheory.MultiplicativeHeights.DegAdd.gramC_eq_mul {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (v : Fin k → Fin r → K) :
    gramC H σ v = (embMat σ v)ᴴ * H * embMat σ v := by sorry
