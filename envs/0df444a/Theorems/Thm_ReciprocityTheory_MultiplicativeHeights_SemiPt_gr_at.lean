-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gr_at
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.gr_at
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:42.981607+00:00
-- url     : https://prove2.me/theorems/1bfeca70-1dc4-498a-ba9d-cb2c60bae567
-- title:
--   Semi Pt: gr at
-- statement:
--   The Semi Pt construction uses the gr at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L10-L16

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.gr_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (j : Fin r) : ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), IsAt j x := by sorry
