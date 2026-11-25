-- Prove2me | Theorems.Thm_P2M_Formalism_LatticeIndexTer_subgroupData_length_chain__bd85a5aaefa7
-- name    : P2M_Formalism_LatticeIndexTer_subgroupData_length_chain__bd85a5aaefa7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:55.966366+00:00
-- url     : https://prove2.me/theorems/a2603b5c-0a1c-41f7-a728-297175ace036
-- title:
--   P2 M Formalism Lattice Index Ter subgroup Data length chain  bd85a5aaefa7: P2 M Formalism Lattice Index Ter subgroup Data length chain  bd85a5aaefa7
-- statement:
--   The P2 M Formalism Lattice Index Ter subgroup Data length chain  bd85a5aaefa7 construction uses the P2 M Formalism Lattice Index Ter subgroup Data length chain  bd85a5aaefa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndex.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndex.lean#L13-L16

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.subgroupData
variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

theorem P2M_Formalism_LatticeIndexTer_subgroupData_length_chain__bd85a5aaefa7 {A B C : Submodule O X} (hAB : A ≤ B) (hBC : B ≤ C) :
    Module.length O (C ⧸ A.comap C.subtype) =
      Module.length O (B ⧸ A.comap B.subtype) + Module.length O (C ⧸ B.comap C.subtype) := by sorry

alias «Formalism».«LatticeIndexTer».«subgroupData».«length_chain'» := P2M_Formalism_LatticeIndexTer_subgroupData_length_chain__bd85a5aaefa7
