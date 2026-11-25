-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_col_mul
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_col_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:25.34039+00:00
-- url     : https://prove2.me/theorems/1a65a95e-237f-4bd0-85f3-a11cccdd97e6
-- title:
--   Multiplicative Heights: sc col mul
-- statement:
--   The Multiplicative Heights construction uses the sc col mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L31-L35

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

theorem ReciprocityTheory.MultiplicativeHeights.sc_col_mul {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι]
    (σ : K →+* ℂ) (N : Matrix (Fin r) (Fin r) K) (c : ι → Fin r → K) :
    embCols σ (fun j => N *ᵥ c j) = N.map σ * embCols σ c := by sorry
