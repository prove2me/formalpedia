-- Prove2me | Theorems.Thm_P2M_Formalism_RepresentationBoundsCohomology_ringDataObjects_r_mem__80118683d757
-- name    : P2M_Formalism_RepresentationBoundsCohomology_ringDataObjects_r_mem__80118683d757
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:24:53.973797+00:00
-- url     : https://prove2.me/theorems/4d0df8f2-a21e-5902-8d3e-98a73dc04e92
-- title:
--   P2 M Formalism Representation Bounds Cohomology ring Data Objects r mem  80118683d757: P2 M Formalism Representation Bounds Cohomology ring Data Objects r mem  80118683d757
-- statement:
--   The P2 M Formalism Representation Bounds Cohomology ring Data Objects r mem  80118683d757 construction uses the P2 M Formalism Representation Bounds Cohomology ring Data Objects r mem  80118683d757 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/FinrankRangeEq.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/FinrankRangeEq.lean#L26-L31

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RankDiagIte
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_BridgeDet
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem P2M_Formalism_RepresentationBoundsCohomology_ringDataObjects_r_mem__80118683d757 {O K : Type} [CommRing O] [CommRing K] [Algebra O K] {X : Type} (T : Subalgebra O (X → O))
    {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Monoid G] (r : G →* (X → Matrix d d K)) (g : G) :
    r g ∈ tSpan T r := by sorry

alias «Formalism».«RepresentationBoundsCohomology».«ringDataObjects».«r_mem'» := P2M_Formalism_RepresentationBoundsCohomology_ringDataObjects_r_mem__80118683d757
