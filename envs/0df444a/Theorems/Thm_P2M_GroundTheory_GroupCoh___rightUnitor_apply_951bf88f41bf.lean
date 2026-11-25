-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___rightUnitor_apply_951bf88f41bf
-- name    : P2M_GroundTheory_GroupCoh___rightUnitor_apply_951bf88f41bf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:52:55.319058+00:00
-- url     : https://prove2.me/theorems/28373113-155f-48ad-8d15-55039846db42
-- title:
--   P2 M Ground Theory Group Coh   right Unitor apply 951bf88f41bf: P2 M Ground Theory Group Coh   right Unitor apply 951bf88f41bf
-- statement:
--   The P2 M Ground Theory Group Coh   right Unitor apply 951bf88f41bf construction uses the P2 M Ground Theory Group Coh   right Unitor apply 951bf88f41bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateCupUnit.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateCupUnit.lean#L45-L50

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

theorem P2M_GroundTheory_GroupCoh___rightUnitor_apply_951bf88f41bf (hE : E.ShortExact)
    (hE' : (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (E.X₃ ⊗ 𝟙_ (Rep.{u} k G)) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (ρ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (ρ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) := by sorry

alias «GroundTheory».«GroupCoh».«δ_rightUnitor_apply» := P2M_GroundTheory_GroupCoh___rightUnitor_apply_951bf88f41bf
