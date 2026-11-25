-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gramC_posDef
-- name    : ReciprocityTheory.MultiplicativeHeights.gramC_posDef
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:03.442167+00:00
-- url     : https://prove2.me/theorems/79ed7092-3364-4e10-a00d-92a05bb19a2d
-- title:
--   Multiplicative Heights: gram C pos Def
-- statement:
--   The Multiplicative Heights construction uses the gram C pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L85-L89

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

theorem ReciprocityTheory.MultiplicativeHeights.gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hH : H.PosDef) (hb : LinearIndependent K b) : (gramC H σ b).PosDef := by sorry
