-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_col_inj
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_col_inj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:03.925692+00:00
-- url     : https://prove2.me/theorems/f9f921dd-63e3-54ca-97c9-08beeac2479e
-- title:
--   Multiplicative Heights: sc col inj
-- statement:
--   The Multiplicative Heights construction uses the sc col inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L37-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L37-L62

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

theorem ReciprocityTheory.MultiplicativeHeights.sc_col_inj {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
    [DecidableEq ι] (σ : K →+* ℂ) {v : ι → Fin r → K} (hv : LinearIndependent K v) :
    Function.Injective (embCols σ v).mulVec := by sorry
