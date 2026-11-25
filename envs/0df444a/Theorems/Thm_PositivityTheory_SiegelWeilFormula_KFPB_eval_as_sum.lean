-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_eval_as_sum
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.eval_as_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:18.319782+00:00
-- url     : https://prove2.me/theorems/0e6f4a17-bc72-4fe2-9c63-e0be6d8a9b42
-- title:
--   KFPB: eval as sum
-- statement:
--   The KFPB construction uses the eval as sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L151-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IntegrablePolyGauss.lean#L151-L156

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
omit [Fintype ι]

theorem PositivityTheory.SiegelWeilFormula.KFPB.eval_as_sum (Q : MvPolynomial ι ℂ) (y : ι → ℂ) :
    eval y Q = ∑ s ∈ Q.support, coeff s Q * eval y (monomial s (1 : ℂ)) := by sorry
