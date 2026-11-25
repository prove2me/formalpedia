-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_kerfam
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_kerfam
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:06.268063+00:00
-- url     : https://prove2.me/theorems/34ae0bea-ea7a-4018-a66f-1db077f89769
-- title:
--   Multiplicative Heights: sc kerfam
-- statement:
--   The Multiplicative Heights construction uses the sc kerfam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractC.lean#L21-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractC.lean#L21-L53

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactSecond_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Module

theorem ReciprocityTheory.MultiplicativeHeights.sc_kerfam {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (N : Matrix (Fin r) (Fin r) K) :
    ∃ b : Fin (finrank K (LinearMap.ker N.mulVecLin)) → Fin r → K,
      (∀ i, b i ∈ L) ∧ (∀ i, N *ᵥ b i = 0) ∧ LinearIndependent K b ∧
      ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b) := by sorry
