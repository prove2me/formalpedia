-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_gramC_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_gramC_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:57.957699+00:00
-- url     : https://prove2.me/theorems/51358e86-9894-5bdd-a76c-74e44adacabc
-- title:
--   Multiplicative Heights: sc gram C eq
-- statement:
--   The Multiplicative Heights construction uses the sc gram C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L13-L20

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

theorem ReciprocityTheory.MultiplicativeHeights.sc_gramC_eq {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embCols σ b)ᴴ * H * embCols σ b := by sorry
