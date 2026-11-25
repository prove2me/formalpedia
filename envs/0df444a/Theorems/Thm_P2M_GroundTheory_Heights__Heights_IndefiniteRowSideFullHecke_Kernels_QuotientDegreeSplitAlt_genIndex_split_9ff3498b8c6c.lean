-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_genIndex_split_9ff3498b8c6c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_genIndex_split_9ff3498b8c6c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:37:08.981883+00:00
-- url     : https://prove2.me/theorems/a1df8d7d-afa1-450a-9099-4cf0f176936e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels Quotient Degree Split Alt gen Index split 9ff3498b8c6c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Ke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels Quotient Degree Split Alt gen Index split 9ff3498b8c6c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels Quotient Degree Split Alt gen Index split 9ff3498b8c6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RelIndexSplitOfLe.lean#L35-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RelIndexSplitOfLe.lean#L35-L73

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_genIndex_split_9ff3498b8c6c {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (π : G →+ G')
    (A C : AddSubgroup G) (hpos : 0 < genIndex A C) :
    genIndex A C = genIndex (A ⊓ π.ker) (C ⊓ π.ker) * genIndex (A.map π) (C.map π) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«QuotientDegreeSplitAlt».«genIndex_split» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_QuotientDegreeSplitAlt_genIndex_split_9ff3498b8c6c
