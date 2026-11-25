-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_append_li
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_append_li
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:08.85135+00:00
-- url     : https://prove2.me/theorems/326cc2ea-661a-4be5-9890-0038b41d50ae
-- title:
--   Multiplicative Heights: sc append li
-- statement:
--   The Multiplicative Heights construction uses the sc append li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractC.lean#L78-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractC.lean#L78-L94

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

theorem ReciprocityTheory.MultiplicativeHeights.sc_append_li {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (N : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hbN : ∀ i, N *ᵥ b i = 0) (hb : LinearIndependent K b)
    (hc : LinearIndependent K (fun j => N *ᵥ c j)) : LinearIndependent K (Fin.append b c) := by sorry
