-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_congr_4a5e25450cfa
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_congr_4a5e25450cfa
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:38.681569+00:00
-- url     : https://prove2.me/theorems/1fb1416a-6d0f-5b58-b9c8-6a84687a4794
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H congr 4a5e25450cfa: P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H congr 4a5e25450cfa
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H congr 4a5e25450cfa construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H congr 4a5e25450cfa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L18-L24

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.CohomologyFunctoriality₂
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {A B C : Cx R}

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_congr_4a5e25450cfa (φ ψ : Hom A B) (h : ∀ n x, φ.f n x = ψ.f n x) (n : ℕ) : φ.H n = ψ.H n := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«Hom».«H_congr» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_congr_4a5e25450cfa
