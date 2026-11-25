-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_colMat_mulVec_injective
-- name    : ReciprocityTheory.MultiplicativeHeights.colMat_mulVec_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:09.108369+00:00
-- url     : https://prove2.me/theorems/a219524d-3d2a-48f3-9d97-2869a68f95a6
-- title:
--   Multiplicative Heights: col Mat mul Vec injective
-- statement:
--   The Multiplicative Heights construction uses the col Mat mul Vec injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L50-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L50-L83

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

theorem ReciprocityTheory.MultiplicativeHeights.colMat_mulVec_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) :
    Function.Injective (colMat σ b).mulVec := by sorry
