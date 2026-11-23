-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_detG_ne_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.detG_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:27.206332+00:00
-- url     : https://prove2.me/theorems/0e972bd1-0176-4237-8b5b-03d01a4201b8
-- title:
--   Semi Pt: det G ne zero
-- statement:
--   The Semi Pt construction uses the det G ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZ.lean#L85-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZ.lean#L85-L115

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.detG_ne_zero {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (hSD : IsSelfDual S L) :
    S.G.det ≠ 0 := by sorry
