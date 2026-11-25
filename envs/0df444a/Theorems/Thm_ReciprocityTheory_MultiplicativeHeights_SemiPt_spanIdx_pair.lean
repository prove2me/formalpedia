-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_spanIdx_pair
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.spanIdx_pair
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:21.90167+00:00
-- url     : https://prove2.me/theorems/50a25b03-86f7-4b09-8937-c47352c1e9d5
-- title:
--   Semi Pt: span Idx pair
-- statement:
--   The Semi Pt construction uses the span Idx pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegH.lean#L37-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegH.lean#L37-L97

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.spanIdx_pair {K : Type} [Field K] [NumberField K] {r : ℕ} (j p : Fin r)
    (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K)) (hj : ∀ x ∈ Gj, IsAt j x)
    (hp : ∀ x ∈ Gp, IsAt p x) (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hy : y ∈ Gp) :
    spanIdx (Gj ⊔ Gp) ![x0, y] = spanIdx Gj ![x0] * spanIdx Gp ![y] := by sorry
