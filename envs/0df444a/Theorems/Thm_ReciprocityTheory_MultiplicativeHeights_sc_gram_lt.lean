-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_gram_lt
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_gram_lt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:11:48.882454+00:00
-- url     : https://prove2.me/theorems/cbbd43a6-81a6-4322-9c75-f6d61e3f0fa7
-- title:
--   Multiplicative Heights: sc gram lt
-- statement:
--   The Multiplicative Heights construction uses the sc gram lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L64-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractB.lean#L64-L249

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

theorem ReciprocityTheory.MultiplicativeHeights.sc_gram_lt {K : Type} [Field K] [NumberField K] {r k m : ℕ} (hm : 0 < m)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) (σ : K →+* ℂ) (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ u : Fin r → ℂ, u ≠ 0 → hq H (N.map σ *ᵥ u) < hq H u)
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hbc : LinearIndependent K (Fin.append b c)) (hb : ∀ i, N *ᵥ b i = 0)
    (hc : LinearIndependent K (fun j => N *ᵥ c j)) :
    0 < (gramC H σ (fun j => N *ᵥ c j)).det.re ∧
      (gramC H σ (fun j => N *ᵥ c j)).det.re < (quotGramC H σ b c).det.re := by sorry
