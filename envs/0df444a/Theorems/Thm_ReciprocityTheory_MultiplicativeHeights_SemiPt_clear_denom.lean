-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_clear_denom
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.clear_denom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:07.408361+00:00
-- url     : https://prove2.me/theorems/bccbd8d4-73f6-5775-a234-1f445392d8ab
-- title:
--   Semi Pt: clear denom
-- statement:
--   The Semi Pt construction uses the clear denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZA.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZA.lean#L69-L72

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.clear_denom {K : Type} [Field K] [NumberField K] {r : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → K)
    (hv : v ∈ Submodule.span K (L : Set (Fin r → K))) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by sorry
