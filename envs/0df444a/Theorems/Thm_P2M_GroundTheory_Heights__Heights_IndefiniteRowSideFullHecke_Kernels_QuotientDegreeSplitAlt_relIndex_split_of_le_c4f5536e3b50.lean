-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_relIndex_split_of_le_c4f5536e3b50
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_relIndex_split_of_le_c4f5536e3b50
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:23:03.617659+00:00
-- url     : https://prove2.me/theorems/2e0fcc1d-a7b8-4243-92d7-7dc72106fcb9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels Quotient Degree Split Alt rel Index split of le c4f5536e3b50: P2 M Ground Theory Heights  Heights Indefinite Row Side Full He
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels Quotient Degree Split Alt rel Index split of le c4f5536e3b50 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels Quotient Degree Split Alt rel Index split of le c4f5536e3b50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RelIndexSplitOfLe.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RelIndexSplitOfLe.lean#L15-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RelIndexSplitOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.QuotientDegreeSplitAlt

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_relIndex_split_of_le_c4f5536e3b50 {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (π : G →+ G')
    {A C : AddSubgroup G} (hCA : C ≤ A) :
    C.relIndex A = C.relIndex (A ⊓ π.ker) * (C.map π).relIndex (A.map π) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«QuotientDegreeSplitAlt».«relIndex_split_of_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_relIndex_split_of_le_c4f5536e3b50
