-- Prove2me | Theorems.Thm_P2M_Formalism_F_span_range_coe_basis__24da96608575
-- name    : P2M_Formalism_F_span_range_coe_basis__24da96608575
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:19:48.1298+00:00
-- url     : https://prove2.me/theorems/04733ad8-2b21-4027-8c7c-bbaf2e17b1c0
-- title:
--   P2 M Formalism F span range coe basis  24da96608575: P2 M Formalism F span range coe basis  24da96608575
-- statement:
--   The P2 M Formalism F span range coe basis  24da96608575 construction uses the P2 M Formalism F span range coe basis  24da96608575 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/DegQuot.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/DegQuot.lean#L70-L73

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F

theorem P2M_Formalism_F_span_range_coe_basis__24da96608575 {E : Type*} [AddCommGroup E] (L : Submodule ℤ E) {ι : Type*}
    (b : Basis ι ℤ L) : span ℤ (Set.range (fun i => (b i : E))) = L := by sorry

alias «Formalism».«F».«span_range_coe_basis'» := P2M_Formalism_F_span_range_coe_basis__24da96608575
