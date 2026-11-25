-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_mid_supp
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.mid_supp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:27.122869+00:00
-- url     : https://prove2.me/theorems/99ff742b-560f-482d-950f-0aa8337f4035
-- title:
--   Semi Pt: mid supp
-- statement:
--   The Semi Pt construction uses the mid supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L62-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L62-L70

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegN
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.mid_supp {K : Type} [Field K] [NumberField K] {r : ℕ} (m : ℕ)
    (Lp : Submodule (𝓞 K) (Fin r → K)) :
    ∀ x ∈ (Lp ⊓ cutSub K r (r - m)).map (projGe K r m), ∀ a : Fin r,
      ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0 := by sorry
