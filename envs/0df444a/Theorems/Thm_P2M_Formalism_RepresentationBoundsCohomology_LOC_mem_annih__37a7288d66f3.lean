-- Prove2me | Theorems.Thm_P2M_Formalism_RepresentationBoundsCohomology_LOC_mem_annih__37a7288d66f3
-- name    : P2M_Formalism_RepresentationBoundsCohomology_LOC_mem_annih__37a7288d66f3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:58.110546+00:00
-- url     : https://prove2.me/theorems/913f80a0-a8ec-4a8f-8c4a-54c6d776835b
-- title:
--   P2 M Formalism Representation Bounds Cohomology LOC mem annih  37a7288d66f3: P2 M Formalism Representation Bounds Cohomology LOC mem annih  37a7288d66f3
-- statement:
--   The P2 M Formalism Representation Bounds Cohomology LOC mem annih  37a7288d66f3 construction uses the P2 M Formalism Representation Bounds Cohomology LOC mem annih  37a7288d66f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/LocDualOrth.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/LocDualOrth.lean#L12-L16

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_LocDualOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC

theorem P2M_Formalism_RepresentationBoundsCohomology_LOC_mem_annih__37a7288d66f3 {O A H : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup H] [Module O H]
    (pr : A →ₗ[O] H →ₗ[O] KO O) (M : Submodule O H) (x : A) :
    x ∈ annih pr M ↔ ∀ m ∈ M, pr x m = 0 := by sorry

alias «Formalism».«RepresentationBoundsCohomology».«LOC».«mem_annih'» := P2M_Formalism_RepresentationBoundsCohomology_LOC_mem_annih__37a7288d66f3
