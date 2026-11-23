-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isCM_quotient_iff
-- name    : ReciprocityTheory.CA.isCM_quotient_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:19.849258+00:00
-- url     : https://prove2.me/theorems/a4ae8d1e-4d0e-4384-bcac-04cc2bc04698
-- title:
--   CA: is CM quotient iff
-- statement:
--   The CA construction uses the is CM quotient iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L119-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/Bridge.lean#L119-L129

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

theorem ReciprocityTheory.CA.isCM_quotient_iff [IsNoetherianRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    IsCM (R ⧸ I) ↔ IsCMMod R (R ⧸ I) := by sorry
