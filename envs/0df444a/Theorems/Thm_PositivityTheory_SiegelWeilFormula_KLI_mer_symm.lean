-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_mer_symm
-- name    : PositivityTheory.SiegelWeilFormula.KLI.mer_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:30.776973+00:00
-- url     : https://prove2.me/theorems/dd12d940-6ae9-4da2-838f-6d4154aad7e3
-- title:
--   KLI: mer symm
-- statement:
--   The KLI construction uses the mer symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussianMomentRealCoords.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussianMomentRealCoords.lean#L9-L11

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_EvalMonomial2
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_GaussianMomentRealCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KLI

theorem PositivityTheory.SiegelWeilFormula.KLI.mer_symm (p : ℝ × ℝ) : Complex.measurableEquivRealProd.symm p = p.1 + p.2 * I := by sorry
