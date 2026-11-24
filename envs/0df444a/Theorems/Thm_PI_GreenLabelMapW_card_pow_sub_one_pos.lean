-- Prove2me | Theorems.Thm_PI_GreenLabelMapW_card_pow_sub_one_pos
-- name    : PI.GreenLabelMapW.card_pow_sub_one_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:27.084155+00:00
-- url     : https://prove2.me/theorems/1904d812-98b6-4fd3-9fa8-c259457e26e0
-- title:
--   Green Label Map W: card pow sub one pos
-- statement:
--   The Green Label Map W construction uses the card pow sub one pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelCharpoly/IrreducibleCharpolyInv.lean#L88-L91

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

theorem PI.GreenLabelMapW.card_pow_sub_one_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ Fintype.card K ^ d - 1 := by sorry
