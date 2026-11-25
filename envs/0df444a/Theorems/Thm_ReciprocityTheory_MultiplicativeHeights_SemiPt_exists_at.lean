-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_exists_at
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.exists_at
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:03.965924+00:00
-- url     : https://prove2.me/theorems/ea4c8d1c-e597-4962-9c27-f7c2761484a5
-- title:
--   Semi Pt: exists at
-- statement:
--   The Semi Pt construction uses the exists at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L18-L29

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.exists_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp) (j : Fin r) :
    ∃ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), x j ≠ 0 := by sorry
