-- Prove2me | Theorems.Thm_PositivityTheory_Lord_invGammaR_zo
-- name    : PositivityTheory.Lord.invGammaR_zo
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:03.943354+00:00
-- url     : https://prove2.me/theorems/0161ddcf-952d-50ac-bc75-078e1f00acac
-- title:
--   Lord: inv Gamma R zo
-- statement:
--   The Lord construction uses the inv Gamma R zo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/InvGammaRZo.lean#L54-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/InvGammaRZo.lean#L54-L96

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

theorem PositivityTheory.Lord.invGammaR_zo (j : ℤ) (hj : j ≤ 0) :
    ZO (fun s => (Gammaℝ s)⁻¹) (j : ℂ) (if Even j then 1 else 0) := by sorry
