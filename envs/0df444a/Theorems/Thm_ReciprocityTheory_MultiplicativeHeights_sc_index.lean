-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_index
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_index
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:38.935096+00:00
-- url     : https://prove2.me/theorems/a71aa019-ce46-540d-bcdf-db4b7173bc5a
-- title:
--   Multiplicative Heights: sc index
-- statement:
--   The Multiplicative Heights construction uses the sc index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractC.lean#L104-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractC.lean#L104-L154

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

theorem ReciprocityTheory.MultiplicativeHeights.sc_index {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (N : Matrix (Fin r) (Fin r) K)
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) (hcL : ∀ j, c j ∈ L)
    (hbN : ∀ i, N *ᵥ b i = 0) (hker : ∀ y, N *ᵥ y = 0 → y ∈ Submodule.span K (Set.range b)) :
    (Submodule.span (𝓞 K) (Set.range fun j => N *ᵥ c j)).toAddSubgroup.relIndex
        (L.map (N.mulVecLin.restrictScalars (𝓞 K))).toAddSubgroup =
      (satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex L.toAddSubgroup := by sorry
