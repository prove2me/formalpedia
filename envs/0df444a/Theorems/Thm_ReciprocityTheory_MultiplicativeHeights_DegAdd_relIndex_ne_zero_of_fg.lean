-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_relIndex_ne_zero_of_fg
-- name    : ReciprocityTheory.MultiplicativeHeights.DegAdd.relIndex_ne_zero_of_fg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:31.555781+00:00
-- url     : https://prove2.me/theorems/d73c3114-0215-41e0-94e5-8988627a2b08
-- title:
--   Deg Add: rel Index ne zero of fg
-- statement:
--   The Deg Add construction uses the rel Index ne zero of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsIntSmulMemSpan.lean#L22-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsIntSmulMemSpan.lean#L22-L47

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactBisAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
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
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open NumberField

theorem ReciprocityTheory.MultiplicativeHeights.DegAdd.relIndex_ne_zero_of_fg {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : L.FG) (v : Fin n → Fin r → K)
    (hv : ∀ x ∈ L, x ∈ Submodule.span K (Set.range v)) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by sorry
