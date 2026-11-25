-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CompatibleChartOperations_mk_eq_zero_iff
-- name    : ReciprocityTheory.Coh.CompatibleChartOperations.mk_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:43.442943+00:00
-- url     : https://prove2.me/theorems/fbd8c792-ed00-4237-8c93-b0bcc8ef0f5b
-- title:
--   Compatible Chart Operations: mk eq zero iff
-- statement:
--   The Compatible Chart Operations construction uses the mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ProdHolds.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ProdHolds.lean#L13-L15

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_ProdHolds
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
open ReciprocityTheory.Coh.CompatibleChartOperations
variable {R : Type u} [CommRing R]

theorem ReciprocityTheory.Coh.CompatibleChartOperations.mk_eq_zero_iff {A : Cx R} {n : ℕ} (x : A.Z n) :
    (Submodule.Quotient.mk x : A.H n) = 0 ↔ x.1 ∈ A.B n := by sorry
