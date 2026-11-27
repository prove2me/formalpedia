-- Prove2me | Theorems.Thm_UpperTheory_V_thmBc_iff
-- name    : UpperTheory.V.thmBc_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:22.751171+00:00
-- url     : https://prove2.me/theorems/995cb720-170a-45f9-afe1-fcad6e4ba1de
-- title:
--   V: thm Bc iff
-- statement:
--   The V construction uses the thm Bc iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean#L112-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean#L112-L134

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top

theorem UpperTheory.V.thmBc_iff {Ct : ℝ} (hC : 1 ≤ Ct) : ThmBc Ct ↔ ThmBcFree := by sorry
