-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_mid_int
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.mid_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:39.780277+00:00
-- url     : https://prove2.me/theorems/03a39375-22b4-5285-8846-368dbb7ba120
-- title:
--   Semi Pt: mid int
-- statement:
--   The Semi Pt construction uses the mid int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L72-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L72-L100

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.mid_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    IsIntegralOn (midForm S m g hfix) ((Lp ⊓ cutSub K r (r - m)).map (projGe K r m)) := by sorry
