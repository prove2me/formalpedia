-- Prove2me | Theorems.Thm_PositivityTheory_Lord_ZO_pow
-- name    : PositivityTheory.Lord.ZO.pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:19.384864+00:00
-- url     : https://prove2.me/theorems/1066aecc-58e6-40bc-af4e-786df0700e9f
-- title:
--   ZO: pow
-- statement:
--   The ZO construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L69-L73

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

theorem PositivityTheory.Lord.ZO.pow (hf : ZO f x m) (n : ℕ) : ZO (fun s => f s ^ n) x (m * n) := by sorry
