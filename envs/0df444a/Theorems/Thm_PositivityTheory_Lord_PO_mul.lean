-- Prove2me | Theorems.Thm_PositivityTheory_Lord_PO_mul
-- name    : PositivityTheory.Lord.PO.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:55.259887+00:00
-- url     : https://prove2.me/theorems/f93d2c79-f946-4e2f-a9cd-6d7290f50be7
-- title:
--   PO: mul
-- statement:
--   The PO construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L22-L28

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open PositivityTheory PositivityTheory.Lord
variable {f g : ℂ → ℂ} {x : ℂ} {k l m n : ℕ}

theorem PositivityTheory.Lord.PO.mul (hf : PO f x k) (hg : PO g x l) : PO (fun s => f s * g s) x (k + l) := by sorry
