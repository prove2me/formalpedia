-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_mem_smul_top_pi
-- name    : ReciprocityTheory.Coh.mem_smul_top_pi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:08.189086+00:00
-- url     : https://prove2.me/theorems/2c198dee-b7ec-508f-b52a-b54876600f96
-- title:
--   Coh: mem smul top pi
-- statement:
--   The Coh construction uses the mem smul top pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FinGen.lean#L69-L79

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
variable {R : Type u} [CommRing R] {M P Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

theorem ReciprocityTheory.Coh.mem_smul_top_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Ideal R) (x : ι → R) :
    x ∈ J • (⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by sorry
