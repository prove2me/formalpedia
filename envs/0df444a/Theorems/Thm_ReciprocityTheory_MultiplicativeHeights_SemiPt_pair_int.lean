-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_pair_int
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.pair_int
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:00.307971+00:00
-- url     : https://prove2.me/theorems/c8eaaa13-ab68-4d64-9c02-10b5af4581f2
-- title:
--   Semi Pt: pair int
-- statement:
--   The Semi Pt construction uses the pair int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L31-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegQ.lean#L31-L60

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.pair_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (h2m : 2 * m ≤ r) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y))
    (j : Fin r) (hj : (j : ℕ) < m) :
    ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j),
      ∀ y ∈ (Lp ⊓ cutSub K r (Fin.rev j + 1)).map (projGe K r (Fin.rev j)),
        IsIntegralElt (S.c (x j) * y (Fin.rev j)) := by sorry
