-- Prove2me | Theorems.Thm_PositivityTheory_Lord_invGammaC_zo
-- name    : PositivityTheory.Lord.invGammaC_zo
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:23.802479+00:00
-- url     : https://prove2.me/theorems/24ce62bb-9c38-424b-88fa-b32c88677d2f
-- title:
--   Lord: inv Gamma C zo
-- statement:
--   The Lord construction uses the inv Gamma C zo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/InvGammaRZo.lean#L98-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/InvGammaRZo.lean#L98-L115

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_InvGammaRZo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex
open scoped Real
open PositivityTheory PositivityTheory.Lord

theorem PositivityTheory.Lord.invGammaC_zo (j : ℤ) (hj : j ≤ 0) : ZO (fun s => (Gammaℂ s)⁻¹) (j : ℂ) 1 := by sorry
