-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_g_ne_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.g_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:02:44.988955+00:00
-- url     : https://prove2.me/theorems/6facb463-0c33-41c6-b9d1-ab7a96ef537f
-- title:
--   Semi Pt: g ne zero
-- statement:
--   The Semi Pt construction uses the g ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZA.lean#L85-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZA.lean#L85-L102

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Definitions.Def_Lemmata_GeneralBFactSecondAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZA
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.g_ne_zero {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0) :
    ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0 := by sorry
