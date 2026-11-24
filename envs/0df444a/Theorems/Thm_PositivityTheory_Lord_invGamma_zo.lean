-- Prove2me | Theorems.Thm_PositivityTheory_Lord_invGamma_zo
-- name    : PositivityTheory.Lord.invGamma_zo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:08.903724+00:00
-- url     : https://prove2.me/theorems/82ce1c32-031b-44f5-8e1b-83c15a5b21c6
-- title:
--   Lord: inv Gamma zo
-- statement:
--   The Lord construction uses the inv Gamma zo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/InvGammaRZo.lean#L8-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/InvGammaRZo.lean#L8-L52

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

theorem PositivityTheory.Lord.invGamma_zo (n : ℕ) : ZO (fun z => (Complex.Gamma z)⁻¹) (-(n : ℂ)) 1 := by sorry
