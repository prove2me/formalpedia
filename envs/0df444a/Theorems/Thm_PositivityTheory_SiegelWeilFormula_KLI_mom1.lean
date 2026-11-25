-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_mom1
-- name    : PositivityTheory.SiegelWeilFormula.KLI.mom1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:16.959471+00:00
-- url     : https://prove2.me/theorems/cd521bd4-878e-4cfc-98b9-d3cd8b5558a1
-- title:
--   KLI: mom1
-- statement:
--   The KLI construction uses the mom1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussianMomentRealCoords.lean#L79-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalOperatorBlocks/GaussianMomentRealCoords.lean#L79-L170

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

theorem PositivityTheory.SiegelWeilFormula.KLI.mom1 (sg : ℤˣ) (t : ℂ) (z : ℂ) (hz : 0 < ((sg : ℤ) : ℝ) * z.im) (α β : ℕ) :
    ∃ q : MvPolynomial Bool ℂ, q.totalDegree ≤ α + β ∧ ∀ ξ : ℂ,
      ∫ w : ℂ, phi1 sg t z ξ α β w =
        eval (fun b => if b then star ξ else ξ) q *
          cexp (2 * Real.pi * I * ((sg : ℤ) : ℂ) * (-((normSq t : ℂ) / 4) * z⁻¹) * (normSq ξ : ℂ)) := by sorry
