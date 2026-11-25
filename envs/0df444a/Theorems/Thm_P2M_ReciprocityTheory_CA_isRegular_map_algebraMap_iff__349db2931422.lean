-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_CA_isRegular_map_algebraMap_iff__349db2931422
-- name    : P2M_ReciprocityTheory_CA_isRegular_map_algebraMap_iff__349db2931422
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:38.891217+00:00
-- url     : https://prove2.me/theorems/113ca9f2-f9f0-4c11-ac77-af7e8af40469
-- title:
--   P2 M Reciprocity Theory CA is Regular map algebra Map iff  349db2931422: P2 M Reciprocity Theory CA is Regular map algebra Map iff  349db2931422
-- statement:
--   The P2 M Reciprocity Theory CA is Regular map algebra Map iff  349db2931422 construction uses the P2 M Reciprocity Theory CA is Regular map algebra Map iff  349db2931422 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L39-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L39-L70

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem P2M_ReciprocityTheory_CA_isRegular_map_algebraMap_iff__349db2931422 {S M : Type*} [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] (rs : List R) :
    IsRegular M (rs.map (algebraMap R S)) ↔ IsRegular M rs := by sorry

alias «ReciprocityTheory».«CA».«isRegular_map_algebraMap_iff'» := P2M_ReciprocityTheory_CA_isRegular_map_algebraMap_iff__349db2931422
