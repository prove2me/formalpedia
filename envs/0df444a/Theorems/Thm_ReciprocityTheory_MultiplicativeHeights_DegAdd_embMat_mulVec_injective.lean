-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_embMat_mulVec_injective
-- name    : ReciprocityTheory.MultiplicativeHeights.DegAdd.embMat_mulVec_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:30.981147+00:00
-- url     : https://prove2.me/theorems/1d371cee-d114-5d60-8b9f-2f0bf1a6d66a
-- title:
--   Deg Add: emb Mat mul Vec injective
-- statement:
--   The Deg Add construction uses the emb Mat mul Vec injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/EmbMatMulVecInjective.lean#L26-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/EmbMatMulVecInjective.lean#L26-L48

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

theorem ReciprocityTheory.MultiplicativeHeights.DegAdd.embMat_mulVec_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    {v : Fin k → Fin r → K} (hv : LinearIndependent K v) :
    Function.Injective (embMat σ v).mulVec := by sorry
