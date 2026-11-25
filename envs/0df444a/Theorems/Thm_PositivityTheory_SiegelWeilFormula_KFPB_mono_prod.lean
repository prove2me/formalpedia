-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_mono_prod
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.mono_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:05.869432+00:00
-- url     : https://prove2.me/theorems/4ea26002-1568-597a-8c9a-31dfdf8c5244
-- title:
--   KFPB: mono prod
-- statement:
--   The KFPB construction uses the mono prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L59-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L59-L71

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalOperatorBlocks_IntgPowQuad
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_eq
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_J_zero
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_intg_pow_quad
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KLI_pk_deg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped FourierTransform
open MeasureTheory Complex MvPolynomial
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KLI (J pk J_eq J_zero intg_pow_quad pk_deg)
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.SiegelWeilFormula.KFPB.mono_prod (b : ℝ) (s : ι →₀ ℕ) (u : EuclideanSpace ℝ ι) (x : ι → ℝ) :
    𝐞 (inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) u) •
      (eval (fun i => (((WithLp.toLp 2 x : EuclideanSpace ℝ ι) i : ℝ) : ℂ)) (monomial s (1 : ℂ)) *
        (Real.exp (-(b * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2)) : ℂ)) =
      ∏ i, phi b (s i) (2 * Real.pi * I * u i) (x i) := by sorry
