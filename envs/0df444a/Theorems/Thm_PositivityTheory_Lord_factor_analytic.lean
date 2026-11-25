-- Prove2me | Theorems.Thm_PositivityTheory_Lord_factor_analytic
-- name    : PositivityTheory.Lord.factor_analytic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:58.094752+00:00
-- url     : https://prove2.me/theorems/89fbfec6-bed3-4cad-b94b-6447d2e2a0c7
-- title:
--   Lord: factor analytic
-- statement:
--   The Lord construction uses the factor analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L14-L16

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

theorem PositivityTheory.Lord.factor_analytic (N : ℕ) (hN : N ≠ 0) (c x : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) x := by sorry
