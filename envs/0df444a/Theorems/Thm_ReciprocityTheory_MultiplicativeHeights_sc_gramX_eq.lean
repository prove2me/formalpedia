-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_gramX_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_gramX_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:14.848884+00:00
-- url     : https://prove2.me/theorems/e5cea03f-7a6c-4536-8f7d-2f0fecc5da8f
-- title:
--   Multiplicative Heights: sc gram X eq
-- statement:
--   The Multiplicative Heights construction uses the sc gram X eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L22-L29

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.sc_gramX_eq {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    gramX H σ b c = (embCols σ b)ᴴ * H * embCols σ c := by sorry
