-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sc_det_lt
-- name    : ReciprocityTheory.MultiplicativeHeights.sc_det_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:45.102293+00:00
-- url     : https://prove2.me/theorems/ffb2eab6-a5a9-56db-af54-63d1fb8d7878
-- title:
--   Multiplicative Heights: sc det lt
-- statement:
--   The Multiplicative Heights construction uses the sc det lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractA.lean#L38-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiContractA.lean#L38-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.sc_det_lt {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {E S : Matrix m m ℂ} (hE : E.PosDef) (hSE : (S - E).PosDef) :
    0 < (E.det).re ∧ (E.det).re < (S.det).re := by sorry
