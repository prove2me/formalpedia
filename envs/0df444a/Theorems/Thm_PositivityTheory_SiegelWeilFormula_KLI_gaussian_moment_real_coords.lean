-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_gaussian_moment_real_coords
-- name    : PositivityTheory.SiegelWeilFormula.KLI.gaussian_moment_real_coords
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:20.310261+00:00
-- url     : https://prove2.me/theorems/19767ac4-0cc5-4b01-bfe4-01f90c5a789c
-- title:
--   KLI: gaussian moment real coords
-- statement:
--   The KLI construction uses the gaussian moment real coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussianMomentRealCoords.lean#L39-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussianMomentRealCoords.lean#L39-L60

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

theorem PositivityTheory.SiegelWeilFormula.KLI.gaussian_moment_real_coords (sg : ℤˣ) (t z ξ : ℂ) (α β : ℕ) (p : ℝ × ℝ) :
    phi1 sg t z ξ α β (p.1 + p.2 * I) =
      eval ![(p.1 : ℂ), (p.2 : ℂ)] (Rab α β) *
        G2 (2 * Real.pi * I * ((sg : ℤ) : ℂ) * z) (lamF t ξ) (muF t ξ) p := by sorry
