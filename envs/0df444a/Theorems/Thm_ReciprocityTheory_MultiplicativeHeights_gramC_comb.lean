-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gramC_comb
-- name    : ReciprocityTheory.MultiplicativeHeights.gramC_comb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:04.329196+00:00
-- url     : https://prove2.me/theorems/9dcad5ed-a20e-50d4-ac68-9d1fd42e1b0b
-- title:
--   Multiplicative Heights: gram C comb
-- statement:
--   The Multiplicative Heights construction uses the gram C comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L32-L37

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

theorem ReciprocityTheory.MultiplicativeHeights.gramC_comb {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (N : Matrix (Fin k) (Fin k) K) :
    gramC H σ (fun j => ∑ i, N i j • b i) = (N.map σ)ᴴ * gramC H σ b * N.map σ := by sorry
