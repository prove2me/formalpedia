-- Prove2me | Theorems.Thm_PositivityTheory_Lord_factor_ne_zero
-- name    : PositivityTheory.Lord.factor_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:13.336355+00:00
-- url     : https://prove2.me/theorems/72967c85-1eec-5ee8-af0c-be0ff7ad0583
-- title:
--   Lord: factor ne zero
-- statement:
--   The Lord construction uses the factor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L18-L33

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FactorDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex NumberField IsDedekindDomain
open PositivityTheory PositivityTheory.Lord

theorem PositivityTheory.Lord.factor_ne_zero (N : ℕ) (hN : 2 ≤ N) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 0 < s.re) :
    1 - c * (N : ℂ) ^ (-s) ≠ 0 := by sorry
