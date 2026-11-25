-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___leftUnitor_apply_453fbefc83a9
-- name    : P2M_GroundTheory_GroupCoh___leftUnitor_apply_453fbefc83a9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:54.839942+00:00
-- url     : https://prove2.me/theorems/f84974f7-6ba7-5023-96b7-898fecdac7e5
-- title:
--   P2 M Ground Theory Group Coh   left Unitor apply 453fbefc83a9: P2 M Ground Theory Group Coh   left Unitor apply 453fbefc83a9
-- statement:
--   The P2 M Ground Theory Group Coh   left Unitor apply 453fbefc83a9 construction uses the P2 M Ground Theory Group Coh   left Unitor apply 453fbefc83a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateCupUnit.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateCupUnit.lean#L38-L43

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateCupUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (E : ShortComplex (Rep.{u} k G))
variable {E}
variable [Fintype G]

theorem P2M_GroundTheory_GroupCoh___leftUnitor_apply_453fbefc83a9 (hE : E.ShortExact)
    (hE' : (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (𝟙_ (Rep.{u} k G) ⊗ E.X₃) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (λ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (λ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) := by sorry

alias «GroundTheory».«GroupCoh».«δ_leftUnitor_apply» := P2M_GroundTheory_GroupCoh___leftUnitor_apply_453fbefc83a9
