-- Prove2me | Theorems.Thm_PositivityTheory_Lord_factor_differentiable
-- name    : PositivityTheory.Lord.factor_differentiable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:39.84505+00:00
-- url     : https://prove2.me/theorems/8bf4cb29-0dac-4161-93c3-30772be5cf11
-- title:
--   Lord: factor differentiable
-- statement:
--   The Lord construction uses the factor differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FactorDifferentiable.lean#L7-L12

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

theorem PositivityTheory.Lord.factor_differentiable (N : ℕ) (hN : N ≠ 0) (c : ℂ) :
    Differentiable ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) := by sorry
