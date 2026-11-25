-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_gen_ne_zero
-- name    : PI.GreenLabelMapW.gen_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:28.669352+00:00
-- url     : https://prove2.me/theorems/e39dbf83-408d-557d-be7b-806560d1eb7e
-- title:
--   Green Label Map W: gen ne zero
-- statement:
--   The Green Label Map W construction uses the gen ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L93-L98

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem PI.GreenLabelMapW.gen_ne_zero (Cv : LabelConv K) {d : ℕ} (hd : 1 ≤ d) : Cv.gen d ≠ 0 := by sorry
