-- Prove2me | Theorems.Thm_PositivityTheory_Lord_PO_of_analytic
-- name    : PositivityTheory.Lord.PO.of_analytic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:32.910735+00:00
-- url     : https://prove2.me/theorems/3c6769cd-27a1-43cd-9833-84a637cbe7a4
-- title:
--   PO: of analytic
-- statement:
--   The PO construction uses the of analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L30-L31

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

theorem PositivityTheory.Lord.PO.of_analytic (hf : AnalyticAt ℂ f x) : PO f x 0 := by sorry
