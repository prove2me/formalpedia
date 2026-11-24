-- Prove2me | Theorems.Thm_PositivityTheory_Lord_ZO_of_analytic
-- name    : PositivityTheory.Lord.ZO.of_analytic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:56.225936+00:00
-- url     : https://prove2.me/theorems/27eb466e-82ae-4dcb-9994-a48e2c05ed65
-- title:
--   ZO: of analytic
-- statement:
--   The ZO construction uses the of analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L75-L76

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

theorem PositivityTheory.Lord.ZO.of_analytic (hf : AnalyticAt ℂ f x) (h0 : f x ≠ 0) : ZO f x 0 := by sorry
