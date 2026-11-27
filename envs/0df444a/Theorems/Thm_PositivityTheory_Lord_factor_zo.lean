-- Prove2me | Theorems.Thm_PositivityTheory_Lord_factor_zo
-- name    : PositivityTheory.Lord.factor_zo
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:13.737867+00:00
-- url     : https://prove2.me/theorems/c792898c-ba41-487d-a00e-50fcc105ffb0
-- title:
--   Lord: factor zo
-- statement:
--   The Lord construction uses the factor zo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L52-L55

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

theorem PositivityTheory.Lord.factor_zo (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ = 1) (j : ℤ) (hj : j ≠ 0) :
    ZO (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) (j : ℂ) 0 := by sorry
