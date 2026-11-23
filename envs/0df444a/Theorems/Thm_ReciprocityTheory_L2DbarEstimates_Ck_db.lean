-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
-- name    : ReciprocityTheory.L2DbarEstimates.Ck.db
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:14.78972+00:00
-- url     : https://prove2.me/theorems/51952ed4-0c37-40d4-83fd-67a7a66b2037
-- title:
--   Ck: db
-- statement:
--   The Ck construction uses the db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean#L202-L205

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.Ck.db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (j : Fin n)
    (f : M → ℂ) (hf : Ck n z (k + 1) f) : Ck n z k (db n z j f) := by sorry
